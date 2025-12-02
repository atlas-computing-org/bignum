/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

/-!
# ARM Instruction Semantics

This file defines the operational semantics of ARM instructions.

Each instruction transforms an `ArmState` to a new `ArmState`.

## References

Source: s2n-bignum/arm/proofs/arm.ml (ARM semantics)
Source: s2n-bignum/arm/tutorial/simple.ml (example execution)
-/

import Bignum.Arm.Machine.Instruction

namespace Bignum.Arm

open Bignum

/--
Execute a single ARM instruction, transforming the state.

This corresponds to the symbolic execution performed by HOL Light's
ARM_STEPS_TAC in the proof.

The simple.ml example shows:
1. ADD X2, X1, X0 with X1=b, X0=a results in X2 = a+b (word add)
2. SUB X2, X2, X1 with X2=a+b, X1=b results in X2 = a

Source: s2n-bignum/arm/tutorial/simple.ml:91-101
The execution is modeled after HOL Light's ARM step function.
-/
def step (instr : Instruction) (s : ArmState) : ArmState :=
  match instr with
  | Instruction.ADD rd rn rm =>
    -- Xd := Xn + Xm (word addition, no flags)
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n + val_m  -- BitVec addition (wraps at 2^64)
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.SUB rd rn rm =>
    -- Xd := Xn - Xm (word subtraction, no flags)
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n - val_m  -- BitVec subtraction (wraps at 2^64)
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.ADDS rd rn rm =>
    -- Xd := Xn + Xm, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let sum_nat := val_n.val + val_m.val
    let result := Word64.ofNat sum_nat
    let carry := sum_nat >= 2^64
    let flags := { s.flags with
      C := carry
      Z := result.val = 0
      N := result.val >= 2^63
    }
    s.write_reg rd result
    |>.write_flags flags
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.SUBS rd rn rm =>
    -- Xd := Xn - Xm, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let diff_nat := val_n.val - val_m.val
    let result := Word64.ofNat diff_nat
    let borrow := val_n.val < val_m.val
    let flags := { s.flags with
      C := !borrow  -- Carry flag is inverted for subtraction
      Z := result.val = 0
      N := result.val >= 2^63
    }
    s.write_reg rd result
    |>.write_flags flags
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.ADCS rd rn rm =>
    -- Xd := Xn + Xm + Carry, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let carry_in := if s.flags.C then 1 else 0
    let sum_nat := val_n.val + val_m.val + carry_in
    let result := Word64.ofNat sum_nat
    let carry := sum_nat >= 2^64
    let flags := { s.flags with
      C := carry
      Z := result.val = 0
      N := result.val >= 2^63
    }
    s.write_reg rd result
    |>.write_flags flags
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.SBCS rd rn rm =>
    -- Xd := Xn - Xm - ~Carry, set flags
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let borrow_in := if s.flags.C then 0 else 1
    let diff_nat := val_n.val - val_m.val - borrow_in
    let result := Word64.ofNat diff_nat
    let borrow := val_n.val < val_m.val + borrow_in
    let flags := { s.flags with
      C := !borrow
      Z := result.val = 0
      N := result.val >= 2^63
    }
    s.write_reg rd result
    |>.write_flags flags
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.AND rd rn rm =>
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n &&& val_m
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.ORR rd rn rm =>
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n ||| val_m
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.EOR rd rn rm =>
    let val_n := s.read_reg rn
    let val_m := s.read_reg rm
    let result := val_n ^^^ val_m
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.LSL rd rn imm =>
    let val_n := s.read_reg rn
    let result := val_n <<< imm
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.LSR rd rn imm =>
    let val_n := s.read_reg rn
    let result := val_n >>> imm
    s.write_reg rd result
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.LDR rd addr =>
    match s.read_mem_word64 addr with
    | some val =>
      s.write_reg rd val
      |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)
    | none => s  -- Memory fault: state unchanged

  | Instruction.STR rd addr =>
    let val := s.read_reg rd
    s.write_mem_word64 addr val
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.MOV rd rn =>
    let val := s.read_reg rn
    s.write_reg rd val
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.MOVZ rd imm =>
    let val := Word64.ofNat imm.toNat
    s.write_reg rd val
    |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)

  | Instruction.RET =>
    -- Return: set PC to X30 (link register)
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
