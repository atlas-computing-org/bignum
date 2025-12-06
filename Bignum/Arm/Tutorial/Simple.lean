/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Spec.Ensures
public import Bignum.Common.Word

@[expose] public section

/-!
# Simple Example: Proving a Simple ARM Program

This is a line-by-line port of s2n-bignum/arm/tutorial/simple.ml with detailed
correspondence documented. The program consists of two instructions:

```asm
0:   8b000022        add     x2, x1, x0
4:   cb010042        sub     x2, x2, x1
```
We prove that starting with X0=a and X1=b, after executing both instructions, we
have X2=a (the additions and subtractions cancel out).

Source: s2n-bignum/arm/tutorial/simple.ml (complete file)
-/

namespace Bignum.Arm.Tutorial
open Bignum Bignum.Arm

/-
In s2n-bignum, the program is defined as a byte sequence:
```ocaml
let simple_mc = new_definition `simple_mc = [
    word 0x22; word 0x00; word 0x00; word 0x8b; // add x2, x1, x0
    word 0x42; word 0x00; word 0x01; word 0xcb  // sub x2, x2, x1
  ]:((8)word)list`;;
```

Or from the object file:
```ocaml
let simple_mc = define_assert_from_elf "simple_mc" "arm/tutorial/simple.o"
[
  0x8b000022;       (* arm_ADD X2 X1 X0 *)
  0xcb010042        (* arm_SUB X2 X2 X1 *)
];;
```

Source: s2n-bignum/arm/tutorial/simple.ml:22-37
-/

/--
The simple program: ADD followed by SUB. In the `base_addr`,  we use 0 for
simplicity; in HOL Light it's symbolic `pc`

Instruction encodings:
- 0x8b000022 = ADD X2, X1, X0
- 0xcb010042 = SUB X2, X2, X1

Source: s2n-bignum/arm/tutorial/simple.ml:28-32
-/
def simple_program (pc : Nat) : Program := {
  base_addr := Word64.ofNat pc
  instructions := [
    Instruction.ADD Reg.X2 Reg.X1 Reg.X0,
    Instruction.SUB Reg.X2 Reg.X2 Reg.X1
  ]
}

/-
In s2n-bignum, the specification is:

```ocaml
let SIMPLE_SPEC = prove(
  `forall pc a b.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) simple_mc /\
         read PC s = word pc /\
         read X0 s = word a /\
         read X1 s = word b)
    // Postcondition
    (\s. read PC s = word (pc+8) /\
         read X2 s = word a)
    // Registers that may change after execution
    (MAYCHANGE [PC;X2])`,
  ...proof tactics...)
```

**Precondition:**
- PC is at the program start
- X0 contains value a
- X1 contains value b
- The program bytes are loaded at PC

**Postcondition:**
- PC has advanced by 8 (two instructions × 4 bytes each)
- X2 contains value a (proof that (a+b)-b = a)

**Frame:**
- Only PC and X2 may change
- All other registers and memory unchanged

Source: s2n-bignum/arm/tutorial/simple.ml:65-84
-/
def simple_spec (pc a b : ℕ) : Ensures := {
  pre := fun s =>
    -- PC is at program start
    s.read_reg Reg.PC = Word64.ofNat pc ∧
    -- X0 contains a
    s.read_reg Reg.X0 = Word64.ofNat a ∧
    -- X1 contains b
    s.read_reg Reg.X1 = Word64.ofNat b ∧
    -- Program is loaded (simplified: we assume exec_program handles this)
    pc % 4 = 0  -- 4-byte alignment

  post := fun s =>
    -- PC advanced by 8 bytes (2 instructions)
    s.read_reg Reg.PC = Word64.ofNat (pc + 8) ∧
    -- X2 contains the original value of X0 (which is a)
    s.read_reg Reg.X2 = Word64.ofNat a

  frame := maychange_regs [Reg.PC, Reg.X2]
  prog := simple_program pc
}


/-
The proof in HOL Light uses these tactics:

```ocaml
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE
```

The key insight:
1. After instruction 1 (ADD): X2 = word(a + b)
2. After instruction 2 (SUB): X2 = word((a + b) - b) = word(a)

The word arithmetic wraps modulo 2^64, so we need to prove:

 (a + b) % 2^64 - b % 2^64 = a % 2^64 (when a, b < 2^64)

Executing the simple program satisfies the
specification. This corresponds to the entire SIMPLE_SPEC theorem in HOL Light.

**Proof outline:**
1. Start with state s₀ satisfying precondition
2. After ADD: X2 = (X1 + X0) = (b + a) = word(a + b)
3. After SUB: X2 = (X2 - X1) = (word(a + b) - b) = word(a)
4. PC advances from pc to pc+4 to pc+8
5. All other registers unchanged

Source: s2n-bignum/arm/tutorial/simple.ml:65-101
-/
theorem simple_correct (pc a b : ℕ)
  : (simple_spec pc a b).satisfies := by
  unfold Ensures.satisfies simple_spec
  simp only
  intro s_init h_pre
  obtain ⟨h_pc, h_x0, h_x1, h_align⟩ := h_pre
  -- PC matches base_addr, program executes
  have h : s_init.read_reg Reg.PC = (simple_program pc).base_addr := by
   unfold simple_program
   simp [h_pc]
  repeat apply And.intro
  · -- PC advances by 8 bytes (4 + 4)
    unfold exec_program ; split_ifs
    unfold exec simple_program
    simp only [List.foldl]
    unfold step
    simp only [BitVec.ofNat_eq_ofNat, ArmState.read_write_same]
    rw [h_pc]
    rw [BitVec.add_assoc]
    unfold Word64.ofNat
    rw [← BitVec.ofNat_add_ofNat]
    simp
  · -- X2 contains a (the arithmetic (a + b) - b = a)
    unfold exec_program ; split_ifs
    unfold exec simple_program
    simp only [List.foldl]
    unfold step
    simp only [BitVec.ofNat_eq_ofNat, ArmState.read_write_same]
    simp only [
     ArmState.read_write_same,
     ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X2),
     ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
     ArmState.read_write_diff _ _ _ _ (by decide : Reg.X2 ≠ Reg.X1)
    ]
    rw [h_x0, h_x1]
    rw [BitVec.add_sub_comm, BitVec.add_comm, BitVec.sub_self, BitVec.add_zero]
  · unfold maychange_regs unchanged_reg
    intro r h_not_changed
    simp only [List.mem_cons] at h_not_changed
    push_neg at h_not_changed
    obtain ⟨h_r_ne_pc, h_r_ne_x2, h₁⟩ := h_not_changed
    clear h₁
    unfold exec_program ; split_ifs
    unfold exec simple_program
    simp only [List.foldl] ; unfold step ; simp
    simp only [
     ArmState.read_write_diff _ _ _ _ (Ne.symm h_r_ne_x2),
     ArmState.read_write_diff _ _ _ _ (Ne.symm h_r_ne_pc)
    ]

end Bignum.Arm.Tutorial
