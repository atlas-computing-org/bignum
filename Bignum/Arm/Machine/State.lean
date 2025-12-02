/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

/-!
# ARM Machine State

This file defines the ARM machine state used for verification.

## Main Definitions

* `Reg` - ARM register names (X0-X30, PC, SP)
* `Flags` - ARM condition flags (N, Z, C, V)
* `ArmState` - Complete machine state (registers, flags, memory)
* `read`, `write` - Access registers and memory

## References

This corresponds to the ARM state in HOL Light's ARM model.
Source: s2n-bignum/arm/proofs/arm.ml and instruction.ml
-/

import Bignum.Common.Memory

namespace Bignum

/--
ARM general-purpose registers and special registers.
-/
inductive Reg
  | X : Fin 31 → Reg  -- X0 through X30
  | PC : Reg           -- Program counter
  | SP : Reg           -- Stack pointer
  deriving DecidableEq, Repr

namespace Reg

-- Convenience constructors for common registers
def X0 : Reg := X 0
def X1 : Reg := X 1
def X2 : Reg := X 2
def X3 : Reg := X 3
def X4 : Reg := X 4
def X5 : Reg := X 5
def X6 : Reg := X 6
def X7 : Reg := X 7
def X8 : Reg := X 8
def X30 : Reg := X 30  -- Link register

end Reg

/--
ARM condition flags.
-/
structure Flags where
  N : Bool  -- Negative
  Z : Bool  -- Zero
  C : Bool  -- Carry
  V : Bool  -- Overflow
  deriving DecidableEq, Repr

/--
Complete ARM machine state.

This corresponds to the `armstate` type in HOL Light.
Source: s2n-bignum/arm/proofs/arm.ml
-/
structure ArmState where
  regs : Reg → Word64    -- Register values
  flags : Flags          -- Condition flags
  mem : Memory           -- Memory state
  deriving Repr

/--
Read a register value from the state.

Corresponds to HOL Light's `read` function.
Example from simple.ml:78: `read X0 s = word a`
-/
def ArmState.read_reg (s : ArmState) (r : Reg) : Word64 :=
  s.regs r

/--
Write a value to a register.

Corresponds to HOL Light's state update for registers.
-/
def ArmState.write_reg (s : ArmState) (r : Reg) (v : Word64) : ArmState :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

/--
Read a byte from memory.
-/
def ArmState.read_mem_byte (s : ArmState) (addr : Address) : Option UInt8 :=
  s.mem.read_byte addr

/--
Write a byte to memory.
-/
def ArmState.write_mem_byte (s : ArmState) (addr : Address) (byte : UInt8) : ArmState :=
  { s with mem := s.mem.write_byte addr byte }

/--
Read a 64-bit word from memory.
-/
def ArmState.read_mem_word64 (s : ArmState) (addr : Address) : Option Word64 :=
  s.mem.read_word64 addr

/--
Write a 64-bit word to memory.
-/
def ArmState.write_mem_word64 (s : ArmState) (addr : Address) (w : Word64) : ArmState :=
  { s with mem := s.mem.write_word64 addr w }

/--
Read a bignum from memory.

Corresponds to HOL Light's `bignum_from_memory`.
Example from bignum_add.ml:91-92:
```ocaml
bignum_from_memory (x,val m) s = a /\
bignum_from_memory (y,val n) s = b
```
-/
def ArmState.read_bignum (s : ArmState) (addr : Address) (n : ℕ) : Option ℕ :=
  s.mem.read_bignum addr n

/--
Write a bignum to memory.
-/
def ArmState.write_bignum (s : ArmState) (addr : Address) (n : ℕ) (val : ℕ) : ArmState :=
  { s with mem := s.mem.write_bignum addr n val }

/--
Update condition flags.
-/
def ArmState.write_flags (s : ArmState) (f : Flags) : ArmState :=
  { s with flags := f }

/--
Convenience notation for reading registers.
Following HOL Light convention: `read PC s` means read program counter from state s.
-/
notation "read_" r:max => fun s : ArmState => s.read_reg r

/--
Helper: Create initial state with given register values.
-/
def ArmState.init (regs : Reg → Word64) (mem : Memory) : ArmState :=
  { regs := regs
    flags := { N := false, Z := false, C := false, V := false }
    mem := mem }

end Bignum
