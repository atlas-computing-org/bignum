/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Common
public import Bignum.Arm.Machine.State
public import Mathlib.Data.Nat.Notation

@[expose] public section

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
  | ADD  : Reg → Reg → Reg → Instruction
  | SUB  : Reg → Reg → Reg → Instruction
  | ADDS : Reg → Reg → Reg → Instruction
  | SUBS : Reg → Reg → Reg → Instruction
  | ADCS : Reg → Reg → Reg → Instruction
  | SBCS : Reg → Reg → Reg → Instruction
  | AND  : Reg → Reg → Reg → Instruction
  | ORR  : Reg → Reg → Reg → Instruction
  | EOR  : Reg → Reg → Reg → Instruction
  | LSL  : Reg → Reg → ℕ → Instruction
  | LSR  : Reg → Reg → ℕ → Instruction
  | LDR  : Reg → Address → Instruction
  | STR  : Reg → Address → Instruction
  | MOV  : Reg → Reg → Instruction
  | MOVZ : Reg → ℕ → ℕ → Instruction  -- MOVZ Rd, #imm, LSL #pos
  | MUL  : Reg → Reg → Reg → Instruction  -- MUL Rd, Rn, Rm (Rd := Rn * Rm)
  | RET  : Instruction
  deriving Repr

/--
Pretty-print an instruction in ARM assembly syntax.
-/
def Instruction.toString : Instruction → String
  | ADD rd rn rm  => s!"ADD {rd}, {rn}, {rm}"
  | SUB rd rn rm  => s!"SUB {rd}, {rn}, {rm}"
  | ADDS rd rn rm => s!"ADDS {rd}, {rn}, {rm}"
  | SUBS rd rn rm => s!"SUBS {rd}, {rn}, {rm}"
  | ADCS rd rn rm => s!"ADCS {rd}, {rn}, {rm}"
  | SBCS rd rn rm => s!"SBCS {rd}, {rn}, {rm}"
  | AND rd rn rm  => s!"AND {rd}, {rn}, {rm}"
  | ORR rd rn rm  => s!"ORR {rd}, {rn}, {rm}"
  | EOR rd rn rm  => s!"EOR {rd}, {rn}, {rm}"
  | LSL rd rn imm => s!"LSL {rd}, {rn}, #{imm}"
  | LSR rd rn imm => s!"LSR {rd}, {rn}, #{imm}"
  | LDR rd addr   => s!"LDR {rd}, [{addr.val}]"
  | STR rd addr   => s!"STR {rd}, [{addr.val}]"
  | MOV rd rn     => s!"MOV {rd}, {rn}"
  | MOVZ rd imm pos => s!"MOVZ {rd}, #{imm}, LSL #{pos}"
  | MUL rd rn rm    => s!"MUL {rd}, {rn}, {rm}"
  | RET             => "RET"

instance : ToString Instruction := ⟨Instruction.toString⟩

/--
A program is a sequence of instructions with a base address (PC).
-/
structure Program where
  base_addr : Word64
  instructions : List Instruction
  deriving Repr

end Bignum.Arm
