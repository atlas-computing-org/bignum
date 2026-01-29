/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Machine.Semantics
public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Ensures Specification System

This file defines the `ensures` specification system used in s2n-bignum proofs.

The formal definition follows HOL Light's `s2n-bignum/common/relational.ml`:

```hol
ensures (step:A->A->bool) precondition postcondition frame <=>
    forall s. precondition s
        ==> eventually step (\s'. postcondition s' /\ frame s s') s
```

Where `eventually` is defined inductively as reachability through the step relation.

## Main Definitions

* `eventually step P s` - `P` is reachable from `s` via `step`
* `ensures step pre post frame` - Hoare triple with frame condition
* `ensures_trans` - Transitivity (ENSURES_TRANS from relational.ml:1373)
-/

namespace Bignum

open Arm

/-!
## Eventually: Reachability Predicate

`eventually step P s` holds if predicate `P` is reachable from state `s`
through the transition relation `step`.

This corresponds to HOL Light's inductive definition (relational.ml:1021-1028):
```hol
(forall s. P s ==> eventually step P s) /\
(forall s. (exists s'. step s s') /\
           (forall s'. step s s' ==> eventually step P s')
             ==> eventually step P s)
```
-/

/--
Reachability predicate: `eventually step P s` holds if `P` is reachable
from `s` via the transition relation `step`.

- **Base case**: If `P s` holds immediately, then `eventually step P s`
- **Inductive case**: If there exists a next step and all next states
  eventually reach `P`, then the current state eventually reaches `P`

Source: s2n-bignum/common/relational.ml:1021-1028
-/
inductive eventually (step : α → α → Prop) (P : α → Prop) : α → Prop where
  | base : P s → eventually step P s
  | ind : (∃ s', step s s') → (∀ s', step s s' → eventually step P s') → eventually step P s

/--
`ensures step pre post frame` is the formal specification that from any state
satisfying `pre`, we eventually reach a state satisfying `post ∧ frame`.

This is the core definition from HOL Light:
```hol
ensures (step:A->A->bool) precondition postcondition frame <=>
    forall s. precondition s
        ==> eventually step (\s'. postcondition s' /\ frame s s') s
```
-/
def ensures (step : α → α → Prop) (pre post : α → Prop) (frame : α → α → Prop) : Prop :=
  ∀ s, pre s → eventually step (fun s' => post s' ∧ frame s s') s

/-!
## Transitivity Theorems

These correspond to ENSURES_TRANS and ENSURES_TRANS_SIMPLE from relational.ml.
-/

/--
Monotonicity of eventually: if `P` implies `Q`, then `eventually P` implies
`eventually Q`.

Source: s2n-bignum/common/relational.ml:1030-1036 (EVENTUALLY_MONO)
-/
theorem eventually_mono {step : α → α → Prop} {P Q : α → Prop}
    (h : ∀ s, P s → Q s) : ∀ s, eventually step P s → eventually step Q s := by
  intro s hev
  induction hev with
  | base hp => exact eventually.base (h _ hp)
  | ind hex hall ih => exact eventually.ind hex (fun s' hs' => ih s' hs')

/--
Transitivity of ensures: composing two ensures specifications.

If we have:
- `ensures step P Q C1` (from P, eventually reach Q with frame C1)
- `ensures step Q R C2` (from Q, eventually reach R with frame C2)

Then:
- `ensures step P R (C1 ,, C2)` (from P, eventually reach R with combined frame)

Source: s2n-bignum/common/relational.ml:1373-1393 (ENSURES_TRANS)
-/
theorem ensures_trans {step : α → α → Prop} {P Q R : α → Prop} {C1 C2 : α → α → Prop}
    (h1 : ensures step P Q C1)
    (h2 : ensures step Q R C2) :
    ensures step P R (fun s s' => C1 s s' ∧ C2 s s') := by
  intro s hp
  have hev1 := h1 s hp
  sorry

/--
Simplified transitivity when frames are the same and idempotent (C ,, C = C).

Source: s2n-bignum/common/relational.ml:1394-1399 (ENSURES_TRANS_SIMPLE)
-/
theorem ensures_trans_simple {step : α → α → Prop} {P Q R : α → Prop}
    {C : α → α → Prop}
    (h_idem : ∀ s s', (C s s' ∧ C s s') ↔ C s s')
    (h1 : ensures step P Q C)
    (h2 : ensures step Q R C) :
    ensures step P R C := by
  have h := ensures_trans h1 h2
  intro s hp
  have hev := h s hp
  exact eventually_mono (fun s' ⟨hr, hc1, hc2⟩ => ⟨hr, (h_idem s s').mp ⟨hc1, hc2⟩⟩) s hev

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
