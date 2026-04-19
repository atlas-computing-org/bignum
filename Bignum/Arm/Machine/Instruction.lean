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

This file defines ARM AArch64 instructions used in s2n-bignum. This will be
expanded to include all instructions needed for bignum operations.

## References

Source: s2n-bignum/arm/proofs/instruction.ml (ARM instruction definitions)
-/

namespace Bignum.Arm

/--
ARM instruction type.

This is a simplified model focusing on the instructions used in s2n-bignum. Each
instruction corresponds to an ARM opcode.
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
  deriving Repr, DecidableEq

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
  | LDR rd addr   => s!"LDR {rd}, [{addr.toNat}]"
  | STR rd addr   => s!"STR {rd}, [{addr.toNat}]"
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

def Program.split (p : Program) (i : Nat) : Program × Program :=
  let first_instrs := p.instructions.take i
  let second_instrs := p.instructions.drop i
  let first_prog := { base_addr := p.base_addr, instructions := first_instrs }
  let second_prog := {
    base_addr := p.base_addr + BitVec.ofNat 64 (i * 4),
    instructions := second_instrs }
  (first_prog, second_prog)

/-!
## ARM Instruction Semantics

This section defines the operational semantics of ARM instructions. Each
instruction transforms an `ArmState` to a new `ArmState`.

The `step` function corresponds to the small-step operational semantics τ ⊆ Σ ×
Σ from the article (Section 4), where execution of a single instruction updates
state s to s'.

## References

Source: s2n-bignum/arm/proofs/arm.ml (ARM semantics)
-/

open Bignum

/--
Advance the program counter by 4 bytes (one instruction width).

This is used by all non-branch instructions to move to the next instruction.
Branch instructions (e.g., RET, B, BL) set PC directly and do not use this helper.

Note: The PC advance reads the *original* PC from `s` (the state before the
instruction's effect), ensuring correct semantics even when the instruction
writes to PC as a side effect.
-/
@[reducible]
def advance_pc (s : ArmState) (s' : ArmState) : ArmState :=
  s'.write_reg Reg.PC (s.read_reg Reg.PC + 4)

/--
Execute a single ARM instruction, transforming the state.

This corresponds to the symbolic execution performed by HOL Light's
ARM_STEPS_TAC in the proof.

For non-branch instructions, `advance_pc` is applied to advance the program
counter by 4 bytes after computing the instruction's effect. Branch
instructions (e.g., RET) set PC directly.
-/
def step (instr : Instruction) (s : ArmState) : ArmState :=
  match instr with
  | Instruction.ADD rd rn rm =>
    -- Xd := Xn + Xm (word addition, no flags)
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n + val_m  -- BitVec addition (wraps at 2^64)
    advance_pc s (s.write_reg rd result)
  | Instruction.SUB rd rn rm =>
    -- Xd := Xn - Xm (word subtraction, no flags)
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n - val_m  -- BitVec subtraction (wraps at 2^64)
    advance_pc s (s.write_reg rd result)
  | Instruction.ADDS rd rn rm =>
    -- Xd := Xn + Xm, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let sum_nat := val_n.toNat + val_m.toNat
    let result := BitVec.ofNat 64 sum_nat
    let carry := sum_nat >= 2^64
    let flags := { s.flags with
      C := carry
      Z := result.toNat = 0
      N := result.toNat >= 2^63
    }
    advance_pc s (s.write_reg rd result |>.write_flags flags)
  | Instruction.SUBS rd rn rm =>
    -- Xd := Xn - Xm, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let diff_nat := val_n.toNat - val_m.toNat
    let result := BitVec.ofNat 64 diff_nat
    let borrow := val_n.toNat < val_m.toNat
    let flags := { s.flags with
      C := !borrow  -- Carry flag is inverted for subtraction
      Z := result.toNat = 0
      N := result.toNat >= 2^63
    }
    advance_pc s (s.write_reg rd result |>.write_flags flags)
  | Instruction.ADCS rd rn rm =>
    -- Xd := Xn + Xm + Carry, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let carry_in := if s.flags.C then 1 else 0
    let sum_nat := val_n.toNat + val_m.toNat + carry_in
    let result := BitVec.ofNat 64 sum_nat
    let carry := sum_nat >= 2^64
    let flags := { s.flags with
      C := carry
      Z := result.toNat = 0
      N := result.toNat >= 2^63
    }
    advance_pc s (s.write_reg rd result |>.write_flags flags)
  | Instruction.SBCS rd rn rm =>
    -- Xd := Xn - Xm - ~Carry, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let borrow_in := if s.flags.C then 0 else 1
    let diff_nat := val_n.toNat - val_m.toNat - borrow_in
    let result := BitVec.ofNat 64 diff_nat
    let borrow := val_n.toNat < val_m.toNat + borrow_in
    let flags := { s.flags with
      C := !borrow
      Z := result.toNat = 0
      N := result.toNat >= 2^63
    }
    advance_pc s (s.write_reg rd result |>.write_flags flags)
  | Instruction.AND rd rn rm =>
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n &&& val_m
    advance_pc s (s.write_reg rd result)
  | Instruction.ORR rd rn rm =>
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n ||| val_m
    advance_pc s (s.write_reg rd result)
  | Instruction.EOR rd rn rm =>
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n ^^^ val_m
    advance_pc s (s.write_reg rd result)
  | Instruction.LSL rd rn imm =>
    let val_n := s.read_reg rn
    let result := val_n <<< imm
    advance_pc s (s.write_reg rd result)
  | Instruction.LSR rd rn imm =>
    let val_n := s.read_reg rn
    let result := val_n >>> imm
    advance_pc s (s.write_reg rd result)
  | Instruction.LDR rd addr =>
    match s.read_mem_word64 addr with
    | some val =>
      advance_pc s (s.write_reg rd val)
    | none => s  -- Memory fault: state unchanged
  | Instruction.STR rd addr =>
    let val := s.read_reg rd
    advance_pc s (s.write_mem_word64 addr val)
  | Instruction.MOV rd rn =>
    let val := s.read_reg rn
    advance_pc s (s.write_reg rd val)
  | Instruction.MOVZ rd imm pos =>
    -- MOVZ: Move wide with zero
    -- Rd := imm * 2^pos (16-bit immediate shifted to position pos)
    -- pos must be 0, 16, 32, or 48
    let val := BitVec.ofNat 64 (imm * 2^pos)
    advance_pc s (s.write_reg rd val)
  | Instruction.MUL rd rn rm =>
    -- MUL: Multiply
    -- Rd := Rn * Rm (low 64 bits of product)
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n * val_m  -- BitVec multiplication (wraps at 2^64)
    advance_pc s (s.write_reg rd result)
  | Instruction.RET =>
    -- Return: set PC to X30 (link register)
    -- Note: RET is a branch instruction and does NOT use advance_pc
    let return_addr := s.read_reg Reg.X30
    s.write_reg Reg.PC return_addr

/--
Execute multiple instructions sequentially.

This corresponds to ARM_STEPS_TAC EXEC (1--n) in HOL Light proofs.
Source: s2n-bignum/arm/tutorial/simple.ml:92 (ARM_STEPS_TAC EXEC (1--2))
-/
def exec (instrs : List Instruction) (s : ArmState) : ArmState :=
  instrs.foldl (fun state instr => step instr state) s

/--
Execute a program from its base address.
-/
def exec_program (prog : Program) (s : ArmState) : ArmState :=
  -- Verify PC is at program start
  if s.read_reg Reg.PC = prog.base_addr then
    exec prog.instructions s
  else
    s  -- PC mismatch: don't execute

end Bignum.Arm
