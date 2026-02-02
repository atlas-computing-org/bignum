/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Spec
public import Bignum.Arm.Machine
public import Bignum.Common.Word

@[expose] public section

/-!
# Simple Example: Proving a Simple ARM Program

This is a line-by-line port of `s2n-bignum/arm/tutorial/simple.ml` with detailed
correspondence documented. The program consists of two instructions:

```asm
0:   8b000022        add     x2, x1, x0
4:   cb010042        sub     x2, x2, x1
```

We prove that starting with `X0 = a` and `X1 = b`, after executing both
instructions, we have `X2 = a` (the additions and subtractions cancel out).

## Memory-Based Model

Following HOL Light's architecture, programs are stored as bytes in memory.
The `arm` step relation fetches, decodes, and executes instructions from memory.

Source: s2n-bignum/arm/tutorial/simple.ml
-/

namespace Bignum.Arm.Tutorial
open Bignum Bignum.Arm

/-!
## Machine Code

The simple program as a byte sequence (machine code).

ARM is little-endian, so:
- Bytes [0x22, 0x00, 0x00, 0x8b] encode instruction 0x8b000022 = ADD X2, X1, X0
- Bytes [0x42, 0x00, 0x01, 0xcb] encode instruction 0xcb010042 = SUB X2, X2, X1
-/

/--
The simple program machine code (8 bytes = 2 instructions).
-/
def simple_mc : List UInt8 :=
  [0x22, 0x00, 0x00, 0x8b,  -- ADD X2, X1, X0
   0x42, 0x00, 0x01, 0xcb]  -- SUB X2, X2, X1

/--
Length of the simple program machine code.
-/
theorem simple_mc_length : simple_mc.length = 8 := by rfl

/-!
## Specification

The specification follows HOL Light's `ensures arm` style:

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

/--
Precondition: program loaded, PC at start, registers initialized.
-/
def simple_pre (pc a b : ℕ) (s : ArmState) : Prop :=
  -- Program bytes are loaded at PC (4-byte aligned)
  aligned_bytes_loaded s.mem (Word64.ofNat pc) simple_mc ∧
  -- PC is at program start
  s.read_reg Reg.PC = Word64.ofNat pc ∧
  -- X0 contains a
  s.read_reg Reg.X0 = Word64.ofNat a ∧
  -- X1 contains b
  s.read_reg Reg.X1 = Word64.ofNat b

/--
Postcondition: PC advanced, X2 contains a.
-/
def simple_post (pc a : ℕ) (s : ArmState) : Prop :=
  -- PC advanced by 8 bytes (2 instructions)
  s.read_reg Reg.PC = Word64.ofNat (pc + 8) ∧
  -- X2 contains the original value of X0 (which is a)
  s.read_reg Reg.X2 = Word64.ofNat a

/-!
## Symbolic Execution Helpers

To prove correctness, we need to show that when bytes are loaded in memory,
`arm_decode` succeeds and returns the expected instruction.
-/

/--
Decode the first instruction (ADD X2, X1, X0) from loaded bytes.
-/
theorem simple_decode_instr1 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc simple_mc) :
    arm_decode s pc = some (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) := by
  sorry

/--
Decode the second instruction (SUB X2, X2, X1) from loaded bytes.
-/
theorem simple_decode_instr2 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc simple_mc) :
    arm_decode s (pc + 4) = some (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) := by
  sorry

/-!
## Main Correctness Theorem

The proof follows HOL Light's structure:
1. ENSURES_INIT_TAC - establish initial state
2. ARM_STEPS_TAC (1--2) - symbolic execution of instructions
3. ENSURES_FINAL_STATE_TAC - verify postcondition
4. WORD_RULE - discharge word arithmetic

The key insight:
1. After instruction 1 (ADD): X2 = word(a + b)
2. After instruction 2 (SUB): X2 = word((a + b) - b) = word(a)
-/

/--
Main correctness theorem: the simple program satisfies its specification. This
corresponds to HOL Light's SIMPLE_SPEC theorem.
-/
theorem simple_correct (pc a b : ℕ) :
    ensures arm
      (simple_pre pc a b)
      (simple_post pc a)
      (maychange_regs [Reg.PC, Reg.X2]) := by
  -- Expand ensures definition
  intro s₀ h_pre
  obtain ⟨h_loaded, h_pc, h_x0, h_x1⟩ := h_pre

  -- Step 1: Execute ADD X2, X1, X0
  -- arm_decode succeeds because bytes are loaded
  apply eventually.ind
  · -- Show there exists a next state
    use step (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) s₀
    unfold arm
    simp only [h_pc, simple_decode_instr1 s₀ (Word64.ofNat pc) h_loaded]
  · -- For all next states, eventually reach goal
    intro s₁ h_step1
    -- s₁ is the state after ADD
    unfold arm at h_step1
    simp only [h_pc, simple_decode_instr1 s₀ (Word64.ofNat pc) h_loaded] at h_step1

    -- Step 2: Execute SUB X2, X2, X1
    apply eventually.ind
    · -- Show there exists a next state
      use step (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) s₁
      -- After ADD, PC = pc + 4
      have h_pc1 : s₁.read_reg Reg.PC = Word64.ofNat pc + 4 := by
        rw [h_step1]
        unfold step
        simp only [ArmState.read_write_same]
        rw [h_pc]
      -- Bytes are still loaded (memory unchanged by ADD)
      have h_loaded1 : aligned_bytes_loaded s₁.mem (Word64.ofNat pc) simple_mc := by
        rw [h_step1]
        unfold step
        simp only [ArmState.write_reg]
        exact h_loaded
      unfold arm
      simp only [h_pc1, simple_decode_instr2 s₁ (Word64.ofNat pc) h_loaded1]
    · -- For all next states, show goal (base case)
      intro s₂ h_step2
      apply eventually.base
      -- s₂ is the final state after SUB
      -- Extract information about s₁ from h_step1
      have h_s1_pc : s₁.read_reg Reg.PC = Word64.ofNat pc + 4 := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same]
        rw [h_pc]
      have h_s1_x2 : s₁.read_reg Reg.X2 = Word64.ofNat b + Word64.ofNat a := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same,
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X2)]
        rw [h_x1, h_x0]
      have h_s1_x1 : s₁.read_reg Reg.X1 = Word64.ofNat b := by
        rw [h_step1] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.X2 ≠ Reg.X1)]
        exact h_x1
      have h_loaded1 : aligned_bytes_loaded s₁.mem (Word64.ofNat pc) simple_mc := by
        rw [h_step1] ; unfold step ; simp only [ArmState.write_reg]
        exact h_loaded

      -- Extract s₂ from h_step2
      unfold arm at h_step2
      simp only [h_s1_pc, simple_decode_instr2 s₁ (Word64.ofNat pc) h_loaded1] at h_step2

      constructor
      · -- Postcondition
        constructor
        · -- PC = pc + 8
          rw [h_step2] ; unfold step
          simp only [ArmState.read_write_same]
          rw [h_s1_pc]
          -- Goal: Word64.ofNat pc + 4 + 4 = Word64.ofNat (pc + 8)
          unfold Word64.ofNat
          simp only [BitVec.add_assoc]
          -- Goal: BitVec.ofNat 64 pc + (4 + 4) = BitVec.ofNat 64 (pc + 8)
          rw [show (4 : BitVec 64) + 4 = 8 by rfl]
          rw [← BitVec.ofNat_add_ofNat]
          rfl
        · -- X2 = a
          rw [h_step2] ; unfold step
          simp only [ArmState.read_write_same,
            ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X2)]
          rw [h_s1_x2, h_s1_x1]
          -- Goal: (b + a) - b = a
          unfold Word64.ofNat
          rw [BitVec.add_comm, BitVec.add_sub_cancel]
      · -- Frame: only PC and X2 changed
        unfold maychange_regs unchanged_reg
        intro r h_not_in
        simp only [List.mem_cons] at h_not_in
        push_neg at h_not_in
        obtain ⟨h_ne_pc, h_ne_x2, _⟩ := h_not_in
        rw [h_step2] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x2),
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]
        rw [h_step1] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x2),
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]

end Bignum.Arm.Tutorial
