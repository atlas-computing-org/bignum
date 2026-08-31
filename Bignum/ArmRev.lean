/-
Copyright (c) 2025 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Guilherme Lima
-/

module

@[expose] public section

set_option autoImplicit false

namespace BigNum.ArmRev

/---
Observable micro-architectural (uarch) events.

Events that can be observed by a side-channel attacker depending on the
inputs of an instruction.
-/

inductive UArchEvent where
  | EventLoad (addr : UInt64) (byte_length : Nat)
  | EventStore (addr : UInt64) (byte_length : Nat)
  | EventJump (src_PC : UInt64) (dest_PC : UInt64)

/--
The ARM machine state.
-/
structure State where
  /-- Program counter. -/
  PC : UInt64

  /-- 31 general purpose registers (0-30) plus SP (register 31). -/
  registers : BitVec 5 → UInt64

  /-- 32 SIMD registers. -/
  simdregisters : BitVec 5 → BitVec 128

  /-- NZCV flags. -/
  flags : BitVec 4

  /-- Byte-addressable memory with 64-bit address space. -/
  memory : UInt64 -> UInt8

  /-- Observable uarch events. -/
  events : List UArchEvent

namespace State

/-- The all zeros state. -/
def allZeros : State := {
  PC            := 0
  registers     := λ _ ↦ 0
  simdregisters := λ _ ↦ 0
  flags         := 0
  memory        := λ _ ↦ 0
  events        := []
}

/-- The all ones state. -/
def allOnes : State := {
  PC            := UInt64.ofBitVec $ BitVec.allOnes 64
  registers     := λ _ ↦ UInt64.ofBitVec $ BitVec.allOnes 64
  simdregisters := λ _ ↦ BitVec.allOnes 128
  flags         := BitVec.allOnes 4
  memory        := λ _ ↦ UInt8.ofBitVec $ BitVec.allOnes 8,
  events        := []
}

instance : Inhabited State where
  default := allZeros

/-- The negative condition flag. -/
def NF (s : State) : Bool :=
  s.flags.getLsb 3

/-- The zero condition flag. -/
def ZF (s : State) : Bool :=
  s.flags.getLsb 2

/-- The carry condition flag. -/
def CF (s : State) : Bool :=
  s.flags.getLsb 1

/-- The overflow condition flag. -/
def VF (s : State) : Bool :=
  s.flags.getLsb 0

/-- The zero register: zero as source, ignored as destination. -/
def XZR (_ : State) : UInt64 :=
  0

@[simp]
theorem XZR_zero (s : State) : s.XZR = 0 := by
  rfl

/-- Main integer registers. -/
def XREG (s : State) (n : Nat) : UInt64 :=
  if n.ble 31 then s.registers n else s.XZR

theorem XREG_eq_zero_of_n_gt_31 (s : State) (n : Nat) :
    n > 31 → s.XREG n = 0 := by
  simp [XREG]; intro h _
  have _ := Nat.not_le_of_gt h; contradiction

def X0 (s : State) : UInt64 := s.XREG 0
def X1 (s : State) : UInt64 := s.XREG 1
def X2 (s : State) : UInt64 := s.XREG 2
def X3 (s : State) : UInt64 := s.XREG 3
def X4 (s : State) : UInt64 := s.XREG 4
def X5 (s : State) : UInt64 := s.XREG 5
def X6 (s : State) : UInt64 := s.XREG 6
def X7 (s : State) : UInt64 := s.XREG 7
def X8 (s : State) : UInt64 := s.XREG 8
def X9 (s : State) : UInt64 := s.XREG 9
def X10 (s : State) : UInt64 := s.XREG 10
def X11 (s : State) : UInt64 := s.XREG 11
def X12 (s : State) : UInt64 := s.XREG 12
def X13 (s : State) : UInt64 := s.XREG 13
def X14 (s : State) : UInt64 := s.XREG 14
def X15 (s : State) : UInt64 := s.XREG 15
def X16 (s : State) : UInt64 := s.XREG 16
def X17 (s : State) : UInt64 := s.XREG 17
def X18 (s : State) : UInt64 := s.XREG 18
def X19 (s : State) : UInt64 := s.XREG 19
def X20 (s : State) : UInt64 := s.XREG 20
def X21 (s : State) : UInt64 := s.XREG 21
def X22 (s : State) : UInt64 := s.XREG 22
def X23 (s : State) : UInt64 := s.XREG 23
def X24 (s : State) : UInt64 := s.XREG 24
def X25 (s : State) : UInt64 := s.XREG 25
def X26 (s : State) : UInt64 := s.XREG 26
def X27 (s : State) : UInt64 := s.XREG 27
def X28 (s : State) : UInt64 := s.XREG 28
def X29 (s : State) : UInt64 := s.XREG 29
def X30 (s : State) : UInt64 := s.XREG 30

/-- Stack pointer. --/
def SP (s : State) : UInt64 :=
  s.XREG 31

/-- 32-bit versions of the main registers. -/
def WREG (s : State) (n : Nat) : UInt32 :=
  UInt32.ofBitVec $ BitVec.truncate 32 (s.XREG n).toBitVec

end State

end BigNum.ArmRev
