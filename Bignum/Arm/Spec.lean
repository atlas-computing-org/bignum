/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Machine.Instruction
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Relation

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

namespace Bignum

open Arm

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
Simplified transitivity when frames are idempotent under relational composition (C ,, C = C).

This holds for MAYCHANGE-style frames where `C s s'` means "only certain components
may differ between s and s'". Such frames are idempotent because if only certain
components may change from s to s₁, and only those same components may change
from s₁ to s', then only those components may change from s to s'.

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

The `arm` step relation defines single-instruction execution.
-/

/--
ARM single-step relation: `arm prog s s'` holds if `s'` is the result of
executing one instruction from state `s` using program `prog`.

This corresponds to the `arm` step relation used in HOL Light's
`ensures arm pre post frame` specifications.
-/
def arm (prog : Program) (s s' : ArmState) : Prop :=
  s.read_reg Reg.PC = prog.base_addr ∧
  match prog.instructions.head? with
  | some instr => s' = step instr s
  | none => False

/-!
## Legacy Structure

The following structure is kept for compatibility with Simple proofs. It
represents a deterministic execution model where a fixed program is executed to
completion.
-/

/--
An ensures specification for ARM programs (legacy/deterministic version).

This corresponds to HOL Light's `ensures arm` construct:
```ocaml
ensures arm
  (\s. precondition)      -- Initial state must satisfy this
  (\s. postcondition)     -- Final state must satisfy this
  (MAYCHANGE [regs...])   -- Frame: what may change
```

Example from simple.ml:
```ocaml
ensures arm
  (\s. aligned_bytes_loaded s (word pc) simple_mc /\
       read PC s = word pc /\
       read X0 s = word a /\
       read X1 s = word b)
  (\s. read PC s = word (pc+8) /\
       read X2 s = word a)
  (MAYCHANGE [PC;X2])
```
-/
structure Ensures where
  pre : ArmState → Prop
  post : ArmState → Prop
  frame : ArmState → ArmState → Prop
  prog : Program

/--
An ensures specification is satisfied if:
For all initial states satisfying the precondition,
executing the program results in a final state that:
1. Satisfies the postcondition
2. Satisfies the frame condition (only allowed things changed)

This corresponds to proving the ensures theorem in HOL Light.
-/
def Ensures.satisfies (spec : Ensures) : Prop :=
  ∀ s_init, spec.pre s_init →
    let s_final := exec_program spec.prog s_init
    spec.post s_final ∧ spec.frame s_init s_final


/-!
## Frame Conditions (MAYCHANGE)

Frame conditions specify which components of the state MAY change during
program execution. Everything not in the frame must remain unchanged.

From relational.ml:
```ocaml
MAYCHANGE [X1; X2; X3]  =  ASSIGNS X1 ,, ASSIGNS X2 ,, ASSIGNS X3
```
-/

/--
A register may change between two states.
-/
def maychange_reg (r : Reg) (s₁ s₂ : ArmState) : Prop :=
  s₁.read_reg r ≠ s₂.read_reg r

/--
A register must not change between two states.
-/
def unchanged_reg (r : Reg) (s₁ s₂ : ArmState) : Prop :=
  s₁.read_reg r = s₂.read_reg r

/--
Memory at an address may change.
-/
def maychange_mem (addr : Address) (s_init s_final : ArmState) : Prop :=
  True  -- Memory location is allowed to change

/--
Memory at an address must not change.
-/
def unchanged_mem (addr : Address) (s_init s_final : ArmState) : Prop :=
  s_final.read_mem_byte addr = s_init.read_mem_byte addr

/--
A memory region may change.
-/
def maychange_mem_region (addr : Address) (size : ℕ) (s_init s_final : ArmState) : Prop :=
  True  -- Memory region is allowed to change

/--
Construct a frame condition from lists of registers and memory regions that may change.

Corresponds to HOL Light's `MAYCHANGE [PC; X2]`.
Example from simple.ml:84: `MAYCHANGE [PC;X2]`
-/
def maychange_regs (regs : List Reg) (s_init s_final : ArmState) : Prop :=
  ∀ r, r ∉ regs → unchanged_reg r s_init s_final

/--
Flags may change.
-/
def maychange_flags (s₁ s₂ : ArmState) : Prop :=
  s₁.flags.N ≠ s₂.flags.N ∨
  s₁.flags.Z ≠ s₂.flags.Z ∨
  s₁.flags.C ≠ s₂.flags.C ∨
  s₁.flags.V ≠ s₂.flags.V

/--
Combine frame conditions.
-/
def maychange_and (f1 f2 : ArmState → ArmState → Prop) : ArmState → ArmState → Prop :=
  fun s_init s_final => f1 s_init s_final ∧ f2 s_init s_final

end Bignum
