/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Common

@[expose] public section

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

namespace Bignum

/--
ARM general-purpose registers and special registers.
-/
inductive Reg
  | X : Fin 31 → Reg   -- X0 through X30
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

instance : ToString Reg where
  toString : Reg → String
  | .X k => s!"X{k}"
  | .PC  => "PC"
  | .SP  => "SP"


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
## ARM machine state

This corresponds to the `armstate` type in HOL Light.
Source: s2n-bignum/arm/proofs/arm.ml
-/
structure ArmState where
  regs : Reg → Word64    -- Register values
  flags : Flags          -- Condition flags
  mem : Memory           -- Memory state

/--
Extensionality theorem for ArmState: two states are equal if all fields are
equal.
-/
@[ext]
theorem ArmState.ext {s1 s2 : ArmState}
    (h_regs : s1.regs = s2.regs)
    (h_flags : s1.flags = s2.flags)
    (h_mem : s1.mem = s2.mem) :
  s1 = s2 := by
  cases s1; cases s2
  congr

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
Convenience notation for reading registers. Following HOL Light convention:
`read PC s` means read program counter from state s.
-/
notation "read_" r:max => fun s : ArmState => ArmState.read_reg s r

/--
Helper: Create initial state with given register values.
-/
def ArmState.init (regs : Reg → Word64) (mem : Memory) : ArmState :=
  { regs := regs
    flags := { N := false, Z := false, C := false, V := false }
    mem := mem }

/-!
## Simplification Lemmas for Register Read/Write

These lemmas enable automatic simplification of register access patterns in
proofs. They are essential for symbolic execution and proving correctness of
instruction sequences.
-/

/--
Reading a register immediately after writing to it returns the written value.
-/
@[simp]
theorem ArmState.read_write_same (s : ArmState) (r : Reg) (v : Word64) :
  (s.write_reg r v).read_reg r = v := by
  unfold write_reg read_reg
  simp

/--
Reading a different register is not affected by a write to another register.
-/
@[simp, scoped grind =]
theorem ArmState.read_write_diff (s : ArmState) (r1 r2 : Reg) (v : Word64)
    (h : r1 ≠ r2) :
  (s.write_reg r1 v).read_reg r2 = s.read_reg r2 := by
  unfold write_reg read_reg
  simp only [ite_eq_right_iff]
  intro h_eq
  subst h_eq
  contradiction

/--
Writing twice to the same register: the second write overwrites the first.
-/
@[simp, scoped grind =]
theorem ArmState.write_write_same (s : ArmState) (r : Reg) (v1 v2 : Word64) :
  (s.write_reg r v1).write_reg r v2 = s.write_reg r v2 := by
  unfold write_reg
  apply ArmState.ext <;> try rfl
  · funext r'
    by_cases h : r' = r
    · subst h; simp
    · simp [h]

/--
Writes to different registers commute.
-/
@[simp, scoped grind =]
theorem ArmState.write_write_comm (s : ArmState) (r1 r2 : Reg) (v1 v2 : Word64)
    (h : r1 ≠ r2) :
  (s.write_reg r1 v1).write_reg r2 v2 = (s.write_reg r2 v2).write_reg r1 v1 := by
  unfold write_reg
  apply ArmState.ext <;> try rfl
  · funext r
    by_cases h1 : r = r1
    · subst h1
      by_cases h2 : r = r2
      · subst h2; contradiction
      · simp [h2]
    · by_cases h2 : r = r2
      · subst h2; simp [h1]
      · simp [h1, h2]

/--
Reading from initial state with explicit register function.
-/
@[simp]
theorem ArmState.read_init (regs : Reg → Word64) (mem : Memory) (r : Reg) :
  (ArmState.init regs mem).read_reg r = regs r := by
  unfold init read_reg
  rfl

end Bignum
