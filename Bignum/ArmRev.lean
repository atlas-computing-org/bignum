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

/-- The empty state. -/
def empty : State :=
  ⟨0, λ _ ↦ 0, λ _ ↦ 0, 0, λ _ ↦ 0, []⟩

instance : Inhabited State where
  default := empty

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
def XZR (s : State) : UInt64 :=
  0

end State

end BigNum.ArmRev
