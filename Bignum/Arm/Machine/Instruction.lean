/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

import Bignum.Arm.Machine.State
public import Mathlib.Data.Nat.Notation

/-!
# ARM Instructions

This file defines ARM AArch64 instructions used in s2n-bignum.

We start with a minimal subset used in the simple.ml tutorial:
- ADD (add two registers)
- SUB (subtract two registers)

This will be expanded to include all instructions needed for bignum operations.

## References

Source: s2n-bignum/arm/proofs/instruction.ml (ARM instruction definitions)
Source: s2n-bignum/arm/tutorial/simple.ml (example: ADD and SUB)
-/

namespace Bignum.Arm

/--
ARM instruction type.

This is a simplified model focusing on the instructions used in s2n-bignum.
Each instruction corresponds to an ARM opcode.

The simple.ml example uses:
- `ADD X2, X1, X0` (encoded as 0x8b000022)
- `SUB X2, X2, X1` (encoded as 0xcb010042)

Source: s2n-bignum/arm/tutorial/simple.ml:17-18, 23-24
-/
inductive Instruction
  | ADD : Reg → Reg → Reg → Instruction
    -- ADD Xd, Xn, Xm: Xd := Xn + Xm
  | SUB : Reg → Reg → Reg → Instruction
    -- SUB Xd, Xn, Xm: Xd := Xn - Xm
  | ADDS : Reg → Reg → Reg → Instruction
    -- ADDS Xd, Xn, Xm: Xd := Xn + Xm, set flags
  | SUBS : Reg → Reg → Reg → Instruction
    -- SUBS Xd, Xn, Xm: Xd := Xn - Xm, set flags
  | ADCS : Reg → Reg → Reg → Instruction
    -- ADCS Xd, Xn, Xm: Xd := Xn + Xm + Carry, set flags
  | SBCS : Reg → Reg → Reg → Instruction
    -- SBCS Xd, Xn, Xm: Xd := Xn - Xm - ~Carry, set flags
  | AND : Reg → Reg → Reg → Instruction
    -- AND Xd, Xn, Xm: Xd := Xn AND Xm
  | ORR : Reg → Reg → Reg → Instruction
    -- ORR Xd, Xn, Xm: Xd := Xn OR Xm
  | EOR : Reg → Reg → Reg → Instruction
    -- EOR Xd, Xn, Xm: Xd := Xn XOR Xm
  | LSL : Reg → Reg → ℕ → Instruction
    -- LSL Xd, Xn, #imm: Xd := Xn << imm
  | LSR : Reg → Reg → ℕ → Instruction
    -- LSR Xd, Xn, #imm: Xd := Xn >> imm (logical)
  | LDR : Reg → Address → Instruction
    -- LDR Xd, [Xn]: Load 64-bit word from memory
  | STR : Reg → Address → Instruction
    -- STR Xd, [Xn]: Store 64-bit word to memory
  | MOV : Reg → Reg → Instruction
    -- MOV Xd, Xn: Xd := Xn (alias for ORR Xd, XZR, Xn)
  | MOVZ : Reg → UInt16 → Instruction
    -- MOVZ Xd, #imm: Xd := imm (zero extend)
  | RET : Instruction
    -- RET: Return (branch to X30)
  deriving Repr

/--
Pretty-print an instruction in ARM assembly syntax.
-/
def Instruction.toString : Instruction → String
  | ADD rd rn rm => s!"ADD {rd}, {rn}, {rm}"
  | SUB rd rn rm => s!"SUB {rd}, {rn}, {rm}"
  | ADDS rd rn rm => s!"ADDS {rd}, {rn}, {rm}"
  | SUBS rd rn rm => s!"SUBS {rd}, {rn}, {rm}"
  | ADCS rd rn rm => s!"ADCS {rd}, {rn}, {rm}"
  | SBCS rd rn rm => s!"SBCS {rd}, {rn}, {rm}"
  | AND rd rn rm => s!"AND {rd}, {rn}, {rm}"
  | ORR rd rn rm => s!"ORR {rd}, {rn}, {rm}"
  | EOR rd rn rm => s!"EOR {rd}, {rn}, {rm}"
  | LSL rd rn imm => s!"LSL {rd}, {rn}, #{imm}"
  | LSR rd rn imm => s!"LSR {rd}, {rn}, #{imm}"
  | LDR rd addr => s!"LDR {rd}, [{addr.val}]"
  | STR rd addr => s!"STR {rd}, [{addr.val}]"
  | MOV rd rn => s!"MOV {rd}, {rn}"
  | MOVZ rd imm => s!"MOVZ {rd}, #{imm}"
  | RET => "RET"

instance : ToString Instruction := ⟨Instruction.toString⟩

/--
A program is a sequence of instructions with a base address (PC).

The simple.ml example has PC at some address `pc` and two instructions.
Source: s2n-bignum/arm/tutorial/simple.ml:22-25
-/
structure Program where
  base_addr : Word64      -- Base PC address where code is loaded
  instructions : List Instruction
  deriving Repr

end Bignum.Arm
