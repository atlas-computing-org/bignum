/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Machine.Decode

@[expose] public section

/-!
# Specification Framework for ARM Verification

This file defines the specification framework for verifying ARM programs,
following the relational Hoare logic approach from s2n-bignum.

The framework is organized following the article "Relational Hoare Logic for
Realistically Modelled Machine Code" (CAV 2025):

## Unary Hoare Logic L₁

* `eventually step P s` - Reachability predicate (operational semantics)
* `ensures step pre post frame` - Hoare triple with frame condition

## Relational Logic L₂ (for future extension)

* `eventuallyn` - Eventually with explicit step count
* `ensuresn` - Stronger ensures with step function
* `ensures2` - Relational Hoare triple for two programs

## Frame Conditions

* `maychange_regs` - MAYCHANGE for registers
* `maychange_mem` - MAYCHANGE for memory

## References

Source: s2n-bignum/common/relational.ml (HOL Light implementation)
-/

namespace Bignum.Arm

/-!
## Operational Semantics - Eventually

`eventually step P s` holds if predicate `P` is reachable from state `s` through
the transition relation `step`.

The two inference rules:
1. **base**: If `P s` already holds, then `eventually step P s`
2. **step**: If there exists a next state AND all next states satisfy
   `eventually step P`, then `eventually step P s`
-/

/--
Reachability predicate: `eventually step P s` holds if `P` is reachable from `s`
via the transition relation `step`.
-/
inductive eventually (step : α → α → Prop) (P : α → Prop) : α → Prop where
  | base : P s → eventually step P s
  | ind (h₁ : ∃ s', step s s') (h₂ : ∀ s', step s s' → eventually step P s')
    : eventually step P s

/-!
## Hoare Triple - Ensures

The `ensures` predicate defines Hoare triples with frame conditions:

> "If precondition `P` holds in state `s`, then following the operational
> semantics (`step`), we **eventually** reach a state `s'` where:
> - The postcondition `Q s'` holds
> - The frame `C s s'` holds (only allowed components changed)"

This corresponds to the axiomatic semantics (Hoare logic) built ON TOP of the
operational semantics (`eventually`).
-/

/--
`ensures step pre post frame` is the formal specification that from any state
satisfying `pre`, we eventually reach a state satisfying `post ∧ frame`.
-/
def ensures (step : α → α → Prop) (pre post : α → Prop)
  (frame : α → α → Prop) : Prop :=
  ∀ s, pre s → eventually step (fun s' => post s' ∧ frame s s') s


/-!
## Theorems for Eventually and Ensures
-/

/--
Monotonicity of eventually: if `P` implies `Q`, then `eventually P` implies
`eventually Q`.
-/
theorem eventually_mono {step : α → α → Prop} {P Q : α → Prop}
    (h : ∀ s, P s → Q s) : ∀ s, eventually step P s → eventually step Q s := by
  intro s hev
  induction hev <;> grind [eventually]

/-!
## Relational Composition

We use Mathlib's `Relation.Comp` for frame composition, which corresponds to
HOL Light's `,,` operator from s2n-bignum/common/relational.ml:26-27:
-/

/-- Notation for relational composition matching HOL Light's `,,` operator. -/
infixr:13 " ,, " => Relation.Comp

theorem eventually_trans {step : α → α → Prop} {P Q : α → Prop}
    (h : ∀ s, P s → eventually step Q s) :
    ∀ s, eventually step P s → eventually step Q s := by
  intro s hev
  induction hev with
  | base hp => exact h _ hp
  | ind hex _ ih => exact eventually.ind hex ih

/--
Transitivity of ensures: composing two ensures specifications.

Source: s2n-bignum/common/relational.ml:1373-1393 (ENSURES_TRANS)
-/
theorem ensures_trans {step : α → α → Prop} {P Q R : α → Prop}
   {C1 C2 : α → α → Prop}
   (h1 : ensures step P Q C1)
   (h2 : ensures step Q R C2) :
   ensures step P R (C1 ,, C2) := by
  intro s₀ hp
  have he1 := h1 s₀ hp
  apply eventually_trans _ _ he1
  intro s₁ ⟨hq, hc1⟩
  have he2 := h2 s₁ hq
  exact eventually_mono (fun s₂ ⟨hr, hc2⟩ => ⟨hr, s₁, hc1, hc2⟩) s₁ he2


/--
Simplified transitivity when frames are idempotent under relational composition
(C ,, C = C).

This holds for MAYCHANGE-style frames where `C s s'` means "only certain
components may differ between s and s'". Such frames are idempotent because if
only certain components may change from s to s₁, and only those same components
may change from s₁ to s', then only those components may change from s to s'.

Source: s2n-bignum/common/relational.ml:1394-1399 (ENSURES_TRANS_SIMPLE)
-/
theorem ensures_trans_simple {step : α → α → Prop} {P Q R : α → Prop}
    {C : α → α → Prop}
    (h_idem : ∀ s₀ s₂, (C ,, C) s₀ s₂ → C s₀ s₂)
    (h1 : ensures step P Q C)
    (h2 : ensures step Q R C) : ensures step P R C := by
  have h := ensures_trans h1 h2
  intro s hp
  have hev := h s hp
  exact eventually_mono (fun s' ⟨hr, hseq⟩ => ⟨hr, h_idem s s' hseq⟩) s hev


/-!
## ARM Step Relation

The `arm` step relation defines single-instruction execution using fetch-decode-
execute from memory, matching HOL Light's architecture where programs live in
memory rather than as a separate structure.
-/

/--
ARM single-step relation: `arm s s'` holds if `s'` is the result of executing
one instruction from state `s`.

This corresponds to HOL Light's `arm` step relation. The execution:
1. Reads the PC
2. Fetches and decodes the instruction at PC from memory
3. Executes the instruction
4. Advances the PC (handled by `step`)

This definition keeps programs in memory, matching the paper's model where
the machine state includes both data and code memory.
-/
def arm (s s' : ArmState) : Prop :=
  let pc := s.read_reg Reg.PC
  match arm_decode s pc with
  | some instr => s' = step instr s
  | none => False

/--
A program (as machine code bytes) is loaded at the given base address.

This corresponds to HOL Light's `aligned_bytes_loaded` combined with a PC check.
Used in preconditions to assert that the program bytes are in memory.
-/
def program_loaded (s : ArmState) (base : Word64) (mc : List UInt8) : Prop :=
  aligned_bytes_loaded s.mem base mc ∧
  s.read_reg Reg.PC = base

/--
Alternative: program bytes loaded without PC constraint.
-/
def program_bytes_loaded (s : ArmState) (base : Word64) (mc : List UInt8) : Prop :=
  aligned_bytes_loaded s.mem base mc

/--
Convenience: `ensures_arm` specialized to the ARM step relation.

This is the primary interface for ARM program verification:
```lean
ensures_arm
  (fun s => program_loaded s base mc ∧ ...)  -- precondition
  (fun s => s.read_reg Reg.PC = ... ∧ ...)   -- postcondition
  (maychange_regs [Reg.PC, ...])             -- frame
```
-/
abbrev ensures_arm := ensures arm


/-!
## Frame Conditions (MAYCHANGE)

Frame conditions specify which components of the state MAY change during
program execution. Everything not in the frame must remain unchanged.

source: s2n-bignum/common/relational.ml

In HOL Light, `ASSIGNS` and `MAYCHANGE` have the following semantics:

```ocaml
(* ASSIGNS c s s' means: there exists some value y such that s' = write c y s *)
(* i.e., s' differs from s only in component c *)
ASSIGNS (c:(A,B)component) s s' <=> exists y. (c := y) s s'

(* MAYCHANGE is relational composition of ASSIGNS *)
MAYCHANGE [] = (=)   (* equality relation: nothing changes *)
MAYCHANGE (CONS c cs) = ASSIGNS c ,, MAYCHANGE cs
```

For example: `MAYCHANGE [PC; X2]` = `ASSIGNS PC ,, ASSIGNS X2`

The key insight is that `ASSIGNS c` is **trivially satisfiable** for any two
states (we can always choose `y = read c s'`). The real constraint comes from
the composition: if only components in the list may change, then all other
components must remain equal.

We use a simplified but equivalent formulation:
- `unchanged_reg r s₁ s₂`: register r has the same value in both states
- `maychange_regs regs s₁ s₂`: all registers NOT in regs are unchanged

**Constructive vs Observational equivalence**: HOL Light's `ASSIGNS c s s'` is
*constructive*: it asserts `s' = write c y s` for some `y`. Our formulation is
*observational*: it only asserts equality of values. These are equivalent when
`write` is "pure" (only affects the target component) and the state has no
hidden fields.
-/

/--
A register must not change between two states.
-/
def unchanged_reg (r : Reg) (s₁ s₂ : ArmState) : Prop :=
  s₁.read_reg r = s₂.read_reg r

/--
Memory at an address must not change.
-/
def unchanged_mem (addr : Address) (s₁ s₂ : ArmState) : Prop :=
  s₁.read_mem_byte addr = s₂.read_mem_byte addr

/--
All flags must not change between two states.
-/
def unchanged_flags (s₁ s₂ : ArmState) : Prop :=
  s₁.flags = s₂.flags

/--
An individual flag must not change between two states.
-/
def unchanged_flag (f : Flag) (s₁ s₂ : ArmState) : Prop :=
  s₁.read_flag f = s₂.read_flag f

/--
`maychange_regs regs s₁ s₂` holds when all registers NOT in `regs` are
unchanged. This is equivalent to HOL Light's `MAYCHANGE [r1; r2; ...]` for
registers: the registers in the list MAY change (no constraint), while all
others must remain equal.

Source: s2n-bignum/common/relational.ml
-/
def maychange_regs (regs : List Reg) (s₁ s₂ : ArmState) : Prop :=
  ∀ r, r ∉ regs → unchanged_reg r s₁ s₂

/--
`maychange_mem addrs s₁ s₂` holds when all memory addresses NOT in `addrs` are
unchanged.
-/
def maychange_mem (addrs : List Address) (s₁ s₂ : ArmState) : Prop :=
  ∀ a, a ∉ addrs → unchanged_mem a s₁ s₂

/--
`maychange_flags flags s₁ s₂` holds when all flags NOT in `flags` are unchanged.

This allows fine-grained control like `MAYCHANGE [CF; ZF]` in HOL Light.

Source: s2n-bignum/arm/proofs/instruction.ml:186-192
-/
def maychange_flags (flags : List Flag) (s₁ s₂ : ArmState) : Prop :=
  ∀ f, f ∉ flags → unchanged_flag f s₁ s₂

/--
Combine frame conditions via conjunction.

When we have `maychange_regs regs ∧ maychange_mem addrs`, both constraints
must hold: registers outside `regs` are unchanged AND memory outside `addrs`
is unchanged.
-/
def maychange_and (f1 f2 : ArmState → ArmState → Prop) :
  ArmState → ArmState → Prop :=
  fun s₁ s₂ => f1 s₁ s₂ ∧ f2 s₁ s₂

infixr:35 " ⊓ " => maychange_and

/-!
## Idempotence of Frame Conditions

A key property for `ensures_trans_simple` is that MAYCHANGE-style frames are
idempotent under relational composition: `C ,, C = C`.

This holds because:
- If only regs R may change from s₀ to s₁, and only R may change from s₁ to s₂
- Then only R may change from s₀ to s₂ (by transitivity of equality on other regs)
-/

/--
`maychange_regs` is idempotent under relational composition.

Source: s2n-bignum/common/relational.ml:188-192 (ASSIGNS_ABSORB_SAME_COMPONENTS)
-/
theorem maychange_regs_idem (regs : List Reg) :
    ∀ s₀ s₂, (maychange_regs regs ,, maychange_regs regs) s₀ s₂ →
             maychange_regs regs s₀ s₂ := by
  intro s₀ s₂ ⟨s₁, h01, h12⟩ r hr
  unfold unchanged_reg
  have eq01 := h01 r hr
  have eq12 := h12 r hr
  unfold unchanged_reg at eq01 eq12
  exact eq01.trans eq12

/--
Reflexivity: `maychange_regs regs s s` always holds (nothing changed).

This corresponds to HOL Light's `(=) subsumed MAYCHANGE [...]`.
-/
theorem maychange_regs_refl (regs : List Reg) (s : ArmState) :
    maychange_regs regs s s := by
  intro r _
  rfl

end Bignum.Arm
