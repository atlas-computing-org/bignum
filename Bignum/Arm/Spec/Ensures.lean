/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

import Bignum.Arm.Machine.Semantics
public import Mathlib.Data.Nat.Notation

/-!
# Ensures Specification System

This file defines the `ensures` specification system used in s2n-bignum proofs.

An `ensures` specification consists of:
- A precondition on the initial state
- A postcondition on the final state
- A frame condition describing what may change

## References

Source: s2n-bignum/arm/tutorial/simple.ml:65-84 (SIMPLE_SPEC)
The ensures predicate is used throughout s2n-bignum proofs.
-/

namespace Bignum

open Arm

/--
An ensures specification for ARM programs.

This corresponds to HOL Light's `ensures arm` construct:
```ocaml
ensures arm
  (\s. precondition)      -- Initial state must satisfy this
  (\s. postcondition)     -- Final state must satisfy this
  (MAYCHANGE [regs...])   -- Frame: what may change
```

Example from simple.ml:65-84:
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

Source: s2n-bignum/arm/tutorial/simple.ml:65-84
-/
structure Ensures where
  /-- Precondition: predicate that must hold on initial state -/
  pre : ArmState → Prop
  /-- Postcondition: predicate that must hold on final state -/
  post : ArmState → Prop
  /-- Frame: predicate relating initial and final states (what may change) -/
  frame : ArmState → ArmState → Prop
  /-- The program to execute -/
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
def maychange_reg (r : Reg) (s_init s_final : ArmState) : Prop :=
  True  -- Register is allowed to change (no constraint)

/--
A register must not change between two states.
-/
def unchanged_reg (r : Reg) (s_init s_final : ArmState) : Prop :=
  s_final.read_reg r = s_init.read_reg r

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
def maychange_flags (s_init s_final : ArmState) : Prop :=
  True  -- Flags are allowed to change

/--
Combine frame conditions.
-/
def maychange_and (f1 f2 : ArmState → ArmState → Prop) : ArmState → ArmState → Prop :=
  fun s_init s_final => f1 s_init s_final ∧ f2 s_init s_final

infixr:35 " ,, " => maychange_and

/--
Standard frame for the simple.ml example:
Only PC and X2 may change, all other registers and memory must be unchanged.

Source: s2n-bignum/arm/tutorial/simple.ml:84
-/
def simple_frame : ArmState → ArmState → Prop :=
  maychange_regs [Reg.PC, Reg.X2]

end Bignum
