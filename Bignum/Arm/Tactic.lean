/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Spec

@[expose] public section

/-!
# Tactic `arm_steps`

The `arm_steps` tactic is the Lean analogue of HOL Light's `ARM_STEPS_TAC`.
It reduces an `ensures arm pre post frame` goal to three simpler obligations:

1. **Decode**: `arm_decode_list instrs s` — the instructions decode correctly
   from memory (usually closed by `by simp [exec_at ...]` or `by decide`)
2. **Post**: `post (exec instrs s)` — postcondition on the computed final state
3. **Frame**: `frame s (exec instrs s)` — frame condition between initial and
   final state

The key insight: instead of manually threading `s₀ → s₁ → s₂` through
`eventually.ind`, we work directly with `exec instrs s₀`, which Lean can
reduce definitionally via `simp [exec, step]`.

## Usage

```lean
theorem SIMPLE_SPEC (pc a b : ℕ) :
    ensures arm pre post (maychange_regs [Reg.PC, Reg.X2]) := by
  intro s₀ ⟨h_loaded, h_pc, h_x0, h_x1⟩
  arm_steps [Instruction.ADD Reg.X2 Reg.X1 Reg.X0,
             Instruction.SUB Reg.X2 Reg.X2 Reg.X1] s₀
    (arm_decode_list_of_aligned_bytes h_loaded (by decide))
  · -- post (exec instrs s₀)
    simp [exec, step, advance_pc, h_pc, h_x0, h_x1]; bv_omega
  · -- frame s₀ (exec instrs s₀)
    intro r hr; simp [exec, step, advance_pc, ArmState.read_write_diff (by decide)]
```

## HOL Light correspondence

```ocaml
ARM_STEPS_TAC EXEC (1--2)  (* HOL Light *)
arm_steps instrs s₀ h_dec  (* Lean *)
```
-/

namespace Bignum.Arm

/--
`arm_steps instrs s h_dec` applies `ensures_of_exec` to split the current goal
into separate post and frame obligations.

The tactic expects the goal to be in the form produced after `intro s₀ h` from
`ensures arm pre post frame`, with `h_dec : arm_decode_list instrs s₀` in context
or provided directly.

Since Lean 4 macros are simpler than Lean 4 tactics for this use case, we
provide `arm_steps_apply` as a theorem that can be applied with `exact` or
`apply`, and `arm_steps` as a convenience syntax wrapping it.
-/
theorem arm_steps_split
    (instrs : List Instruction)
    (s : ArmState)
    (h_dec : arm_decode_list instrs s)
    {post : ArmState → Prop}
    {frame : ArmState → ArmState → Prop}
    (h_post : post (exec instrs s))
    (h_frame : frame s (exec instrs s)) :
    eventually arm (fun s' => post s' ∧ frame s s') s :=
  eventually_mono
    (fun _ heq => heq ▸ ⟨h_post, h_frame⟩)
    s
    (eventually_exec instrs s h_dec)

/--
Tactic macro: `arm_steps instrs s h_dec` splits an `eventually` goal into
post and frame subgoals, after establishing that the instructions decode.

Usage in a proof after `intro s₀ h`:
```lean
  apply arm_steps_split instrs s₀ h_dec
  · -- Goal: post (exec instrs s₀)
  · -- Goal: frame s₀ (exec instrs s₀)
```
-/
macro "arm_steps" instrs:term " from " s:term " via " h_dec:term : tactic =>
  `(tactic| apply arm_steps_split $instrs $s $h_dec)

end Bignum.Arm
