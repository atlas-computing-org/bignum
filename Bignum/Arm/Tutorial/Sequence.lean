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
# Sequence Example: Proving by Sequential Composition

This is a line-by-line port of `s2n-bignum/arm/tutorial/sequence.ml`.

The key technique demonstrated is **compositional verification**: instead of
symbolically executing all instructions at once, we split the program into
sequential chunks with intermediate assertions.

## The Program

```asm
0:   8b000021        add     x1, x1, x0
4:   8b000042        add     x2, x2, x0
8:   d2800043        mov     x3, #0x2
c:   9b037c21        mul     x1, x1, x3
```

## The Approach

1. Split at pc+8 into two chunks:
   - First chunk (pc to pc+8): two `add` instructions
   - Second chunk (pc+8 to pc+16): `mov` and `mul`

2. Intermediate assertion at pc+8: `X1 = a + b`

3. Prove each chunk independently and compose the proofs.

## Memory-Based Model

Following HOL Light's architecture, programs are stored as bytes in memory.
The `arm` step relation fetches, decodes, and executes instructions from memory.
-/

namespace Bignum.Arm.Tutorial
open Bignum Bignum.Arm

/-!
## Machine Code

The sequence program machine code (16 bytes = 4 instructions).

ARM is little-endian, so:
- Bytes [0x21, 0x00, 0x00, 0x8b] encode instruction 0x8b000021 = ADD X1, X1, X0
- Bytes [0x42, 0x00, 0x00, 0x8b] encode instruction 0x8b000042 = ADD X2, X2, X0
- Bytes [0x43, 0x00, 0x80, 0xd2] encode instruction 0xd2800043 = MOV X3, #2
- Bytes [0x21, 0x7c, 0x03, 0x9b] encode instruction 0x9b037c21 = MUL X1, X1, X3
-/
def sequence_mc : List UInt8 :=
  [0x21, 0x00, 0x00, 0x8b,  -- ADD X1, X1, X0
   0x42, 0x00, 0x00, 0x8b,  -- ADD X2, X2, X0
   0x43, 0x00, 0x80, 0xd2,  -- MOV X3, #2
   0x21, 0x7c, 0x03, 0x9b]  -- MUL X1, X1, X3


/-!
## Specification

The specification follows HOL Light's `ensures arm` style:

```ocaml
ensures arm
  (\s. aligned_bytes_loaded s (word pc) sequence_mc /\
       read PC s = word pc /\
       read X0 s = word a /\
       read X1 s = word b /\
       read X2 s = word c)
  (\s. read PC s = word (pc+16) /\
       read X1 s = word ((a + b) * 2))
  (MAYCHANGE [PC;X1;X2;X3])
```
-/

/--
Precondition: program loaded, PC at start, registers initialized.
-/
def sequence_pre (pc a b c : ℕ) (s : ArmState) : Prop :=
  aligned_bytes_loaded s.mem (Word64.ofNat pc) sequence_mc ∧
  s.read_reg Reg.PC = Word64.ofNat pc ∧
  s.read_reg Reg.X0 = Word64.ofNat a ∧
  s.read_reg Reg.X1 = Word64.ofNat b ∧
  s.read_reg Reg.X2 = Word64.ofNat c

/--
Intermediate assertion at pc+8: X1 = a + b.

This is the `\s. read X1 s = word (a + b)` from HOL Light's
`ENSURES_SEQUENCE_TAC`.

Source: s2n-bignum/arm/tutorial/sequence.ml:77
-/
def sequence_mid (pc a b : ℕ) (s : ArmState) : Prop :=
  aligned_bytes_loaded s.mem (Word64.ofNat pc) sequence_mc ∧
  s.read_reg Reg.PC = Word64.ofNat (pc + 8) ∧
  s.read_reg Reg.X1 = Word64.ofNat (a + b)

/--
Postcondition: PC at pc+16, X1 = (a+b)*2.
-/
def sequence_post (pc a b : ℕ) (s : ArmState) : Prop :=
  s.read_reg Reg.PC = Word64.ofNat (pc + 16) ∧
  s.read_reg Reg.X1 = Word64.ofNat ((a + b) * 2)

/-!
## Symbolic Execution Helpers

Decode lemmas for each instruction in the sequence program.
-/

/-- Decode instruction 1: ADD X1, X1, X0 -/
theorem sequence_decode_instr1 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s pc = some (Instruction.ADD Reg.X1 Reg.X1 Reg.X0) := by
  obtain ⟨_, h_bytes⟩ := h
  have h0 : s.mem.read_byte pc = some 0x21 := by
    have := h_bytes 0 (by decide : 0 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    exact (BitVec.add_zero pc).symm
  have h1 : s.mem.read_byte (pc + 1) = some 0x00 := by
    have := h_bytes 1 (by decide : 1 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
  have h2 : s.mem.read_byte (pc + 2) = some 0x00 := by
    have := h_bytes 2 (by decide : 2 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
  have h3 : s.mem.read_byte (pc + 3) = some 0x8b := by
    have := h_bytes 3 (by decide : 3 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
  unfold arm_decode read4Bytes
  simp only [h0, h1, h2, h3]
  rfl

/-- Decode instruction 2: ADD X2, X2, X0 -/
theorem sequence_decode_instr2 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s (pc + 4) = some (Instruction.ADD Reg.X2 Reg.X2 Reg.X0) := by
  obtain ⟨_, h_bytes⟩ := h
  have h4 : s.mem.read_byte (pc + 4) = some 0x42 := by
    have := h_bytes 4 (by decide : 4 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
  have h5 : s.mem.read_byte (pc + 4 + 1) = some 0x00 := by
    have := h_bytes 5 (by decide : 5 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  have h6 : s.mem.read_byte (pc + 4 + 2) = some 0x00 := by
    have := h_bytes 6 (by decide : 6 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  have h7 : s.mem.read_byte (pc + 4 + 3) = some 0x8b := by
    have := h_bytes 7 (by decide : 7 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  unfold arm_decode read4Bytes
  simp only [h4, h5, h6, h7]
  rfl

/-- Decode instruction 3: MOV X3, #2 (encoded as MOVZ) -/
theorem sequence_decode_instr3 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s (pc + 8) = some (Instruction.MOVZ Reg.X3 2 0) := by
  obtain ⟨_, h_bytes⟩ := h
  have h8 : s.mem.read_byte (pc + 8) = some 0x43 := by
    have := h_bytes 8 (by decide : 8 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
  have h9 : s.mem.read_byte (pc + 8 + 1) = some 0x00 := by
    have := h_bytes 9 (by decide : 9 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  have h10 : s.mem.read_byte (pc + 8 + 2) = some 0x80 := by
    have := h_bytes 10 (by decide : 10 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  have h11 : s.mem.read_byte (pc + 8 + 3) = some 0xd2 := by
    have := h_bytes 11 (by decide : 11 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  unfold arm_decode read4Bytes
  simp only [h8, h9, h10, h11]
  rfl

/-- Decode instruction 4: MUL X1, X1, X3 -/
theorem sequence_decode_instr4 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s (pc + 12) = some (Instruction.MUL Reg.X1 Reg.X1 Reg.X3) := by
  obtain ⟨_, h_bytes⟩ := h
  have h12 : s.mem.read_byte (pc + 12) = some 0x21 := by
    have := h_bytes 12 (by decide : 12 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
  have h13 : s.mem.read_byte (pc + 12 + 1) = some 0x7c := by
    have := h_bytes 13 (by decide : 13 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  have h14 : s.mem.read_byte (pc + 12 + 2) = some 0x03 := by
    have := h_bytes 14 (by decide : 14 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  have h15 : s.mem.read_byte (pc + 12 + 3) = some 0x9b := by
    have := h_bytes 15 (by decide : 15 < 16)
    simp only [sequence_mc, Word64.ofNat] at this
    convert this using 2
    bv_omega
  unfold arm_decode read4Bytes
  simp only [h12, h13, h14, h15]
  rfl

/-!
## Compositional Verification

The key insight from sequence.ml is that we can split a program into sequential
chunks and prove each separately. This corresponds to HOL Light's
`ENSURES_SEQUENCE_TAC`.

Given:
- ensures arm pre mid frame1  (for first chunk)
- ensures arm mid post frame2 (for second chunk)

We can derive:
- ensures arm pre post (frame1 ∪ frame2)  (for whole program)
-/

/--
Sequential composition of ensures: if we can prove ensures for two sequential
chunks, we can derive ensures for the whole program.

This corresponds to HOL Light's `ENSURES_SEQUENCE_TAC`.
-/
theorem ensures_sequence
    {step : α → α → Prop}
    (pre mid post : α → Prop)
    (frame : α → α → Prop)
    (h1 : ensures step pre mid frame)
    (h2 : ensures step mid post frame)
    (h_frame_trans : ∀ s1 s2 s3, frame s1 s2 → frame s2 s3 → frame s1 s3) :
    ensures step pre post frame := by
  intro s₀ h_pre
  have h_ev1 := h1 s₀ h_pre
  apply eventually_trans _ _ h_ev1
  intro s₁ ⟨h_mid, h_f1⟩
  have h_ev2 := h2 s₁ h_mid
  exact eventually_mono (fun s₂ hpost_frame =>
    ⟨hpost_frame.1, h_frame_trans s₀ s₁ s₂ h_f1 hpost_frame.2⟩) s₁ h_ev2

/--
Frame transitivity for maychange_regs.
-/
theorem maychange_regs_trans (regs : List Reg) :
    ∀ s1 s2 s3, maychange_regs regs s1 s2 →
                maychange_regs regs s2 s3 →
                maychange_regs regs s1 s3 := by
  intro s1 s2 s3 h12 h23
  unfold maychange_regs unchanged_reg at *
  intro r hr
  rw [h12 r hr, h23 r hr]

/-!
## Chunk Proofs

First chunk: instructions 1-2 (two ADD instructions)
Second chunk: instructions 3-4 (MOV and MUL)
-/

/--
First chunk specification: the two ADD instructions.

Precondition: PC at start, X0 = a, X1 = b, X2 = c
Postcondition: PC at pc+8, X1 = a + b

Source: s2n-bignum/arm/tutorial/sequence.ml:80-92
-/
theorem sequence_chunk1_correct (pc a b c : ℕ) :
    ensures arm
      (sequence_pre pc a b c)
      (sequence_mid pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) := by
  intro s₀ h_pre
  obtain ⟨h_loaded, h_pc, h_x0, h_x1, h_x2⟩ := h_pre
  -- Step 1: Execute ADD X1, X1, X0
  apply eventually.ind
  · use step (Instruction.ADD Reg.X1 Reg.X1 Reg.X0) s₀
    unfold arm
    simp only [h_pc, sequence_decode_instr1 s₀ (Word64.ofNat pc) h_loaded]
  · intro s₁ h_step1
    unfold arm at h_step1
    simp only [h_pc, sequence_decode_instr1 s₀ (Word64.ofNat pc) h_loaded] at h_step1
    -- Step 2: Execute ADD X2, X2, X0
    apply eventually.ind
    · have h_pc1 : s₁.read_reg Reg.PC = Word64.ofNat pc + 4 := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same]
        rw [h_pc]
      have h_loaded1 : aligned_bytes_loaded s₁.mem (Word64.ofNat pc) sequence_mc := by
        rw [h_step1] ; unfold step ; simp only [ArmState.write_reg]
        exact h_loaded
      use step (Instruction.ADD Reg.X2 Reg.X2 Reg.X0) s₁
      unfold arm
      simp only [h_pc1, sequence_decode_instr2 s₁ (Word64.ofNat pc) h_loaded1]
    · intro s₂ h_step2
      apply eventually.base
      -- Extract s₁ properties
      have h_s1_pc : s₁.read_reg Reg.PC = Word64.ofNat pc + 4 := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same]
        rw [h_pc]
      have h_s1_x1 : s₁.read_reg Reg.X1 = Word64.ofNat b + Word64.ofNat a := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same,
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1)]
        rw [h_x1, h_x0]
      have h_loaded1 : aligned_bytes_loaded s₁.mem (Word64.ofNat pc) sequence_mc := by
        rw [h_step1] ; unfold step ; simp only [ArmState.write_reg]
        exact h_loaded
      -- Extract s₂ from h_step2
      unfold arm at h_step2
      simp only [h_s1_pc, sequence_decode_instr2 s₁ (Word64.ofNat pc) h_loaded1] at h_step2
      constructor
      · -- Postcondition: sequence_mid
        unfold sequence_mid
        constructor
        · -- Memory still loaded
          rw [h_step2] ; unfold step ; simp only [ArmState.write_reg]
          exact h_loaded1
        constructor
        · -- PC = pc + 8
          rw [h_step2] ; unfold step
          simp only [ArmState.read_write_same]
          rw [h_s1_pc]
          unfold Word64.ofNat
          simp only [BitVec.add_assoc]
          rw [show (4 : BitVec 64) + 4 = 8 by rfl]
          rw [← BitVec.ofNat_add_ofNat]
          rfl
        · -- X1 = a + b
          rw [h_step2] ; unfold step
          simp only [
            ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
            ArmState.read_write_diff _ _ _ _ (by decide : Reg.X2 ≠ Reg.X1)]
          rw [h_s1_x1]
          unfold Word64.ofNat
          rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]
      · -- Frame: only PC, X1, X2, X3 may change
        unfold maychange_regs unchanged_reg
        intro r h_not_in
        simp only [List.mem_cons] at h_not_in
        push_neg at h_not_in
        obtain ⟨h_ne_pc, h_ne_x1, h_ne_x2, h_ne_x3, _⟩ := h_not_in
        rw [h_step2] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x2),
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]
        rw [h_step1] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x1),
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]

/--
Second chunk specification: MOV x3, #2 and MUL x1, x1, x3.

Precondition: PC at pc+8, X1 = a + b (from intermediate assertion)
Postcondition: PC at pc+16, X1 = (a + b) * 2

Source: s2n-bignum/arm/tutorial/sequence.ml:95-100
-/
theorem sequence_chunk2_correct (pc a b : ℕ) :
    ensures arm
      (sequence_mid pc a b)
      (sequence_post pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) := by
  intro s₀ h_mid
  obtain ⟨h_loaded, h_pc, h_x1⟩ := h_mid
  -- Key: convert Word64.ofNat (pc + 8) to Word64.ofNat pc + 8
  have h_pc_eq : Word64.ofNat (pc + 8) = Word64.ofNat pc + 8 := by
    unfold Word64.ofNat; rw [← BitVec.ofNat_add_ofNat]; rfl
  rw [h_pc_eq] at h_pc
  -- Decode lemma for instruction 3 at this state
  have h_dec3 := sequence_decode_instr3 s₀ (Word64.ofNat pc) h_loaded
  -- Step 1: Execute MOVZ X3, #2
  apply eventually.ind
  · use step (Instruction.MOVZ Reg.X3 2 0) s₀
    unfold arm
    simp only [h_pc, h_dec3]
  · intro s₁ h_step1
    unfold arm at h_step1
    simp only [h_pc, h_dec3] at h_step1
    -- Step 2: Execute MUL X1, X1, X3
    apply eventually.ind
    · have h_pc1 : s₁.read_reg Reg.PC = Word64.ofNat pc + 12 := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same]
        rw [h_pc]
        unfold Word64.ofNat
        simp only [BitVec.add_assoc]
        rw [show (8 : BitVec 64) + 4 = 12 by rfl]
      have h_loaded1 : aligned_bytes_loaded s₁.mem (Word64.ofNat pc) sequence_mc := by
        rw [h_step1] ; unfold step ; simp only [ArmState.write_reg]
        exact h_loaded
      use step (Instruction.MUL Reg.X1 Reg.X1 Reg.X3) s₁
      unfold arm
      simp only [h_pc1, sequence_decode_instr4 s₁ (Word64.ofNat pc) h_loaded1]
    · intro s₂ h_step2
      apply eventually.base
      -- Extract s₁ properties
      have h_s1_pc : s₁.read_reg Reg.PC = Word64.ofNat pc + 12 := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same]
        rw [h_pc]
        unfold Word64.ofNat
        simp only [BitVec.add_assoc]
        rw [show (8 : BitVec 64) + 4 = 12 by rfl]
      have h_s1_x1 : s₁.read_reg Reg.X1 = Word64.ofNat (a + b) := by
        rw [h_step1] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.X3 ≠ Reg.X1)]
        exact h_x1
      have h_s1_x3 : s₁.read_reg Reg.X3 = Word64.ofNat (2 * 2 ^ 0) := by
        rw [h_step1] ; unfold step
        simp only [ArmState.read_write_same,
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X3)]
      have h_loaded1 : aligned_bytes_loaded s₁.mem (Word64.ofNat pc) sequence_mc := by
        rw [h_step1] ; unfold step ; simp only [ArmState.write_reg]
        exact h_loaded
      -- Extract s₂ from h_step2
      unfold arm at h_step2
      simp only [h_s1_pc, sequence_decode_instr4 s₁ (Word64.ofNat pc) h_loaded1] at h_step2
      constructor
      · -- Postcondition: sequence_post
        unfold sequence_post
        constructor
        · -- PC = pc + 16
          rw [h_step2] ; unfold step
          simp only [ArmState.read_write_same]
          rw [h_s1_pc]
          unfold Word64.ofNat
          simp only [BitVec.add_assoc]
          rw [show (12 : BitVec 64) + 4 = 16 by rfl]
          rw [← BitVec.ofNat_add_ofNat]
          rfl
        · -- X1 = (a + b) * 2
          rw [h_step2] ; unfold step
          simp only [ArmState.read_write_same,
            ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1)]
          rw [h_s1_x1, h_s1_x3]
          unfold Word64.ofNat
          simp only [show 2 * 2 ^ 0 = 2 by norm_num]
          rw [← BitVec.ofNat_mul_ofNat]
      · -- Frame: only PC, X1, X2, X3 may change
        unfold maychange_regs unchanged_reg
        intro r h_not_in
        simp only [List.mem_cons] at h_not_in
        push_neg at h_not_in
        obtain ⟨h_ne_pc, h_ne_x1, _, h_ne_x3, _⟩ := h_not_in
        rw [h_step2] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x1),
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]
        rw [h_step1] ; unfold step
        simp only [
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x3),
          ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]

/-!
## Main Correctness Theorem

Compose the two chunk proofs to get the full program correctness.
-/

/--
Main correctness theorem: the sequence program satisfies its specification.

The proof demonstrates compositional verification:
1. Split the program at pc+8
2. Prove chunk1 establishes the intermediate assertion (X1 = a + b)
3. Prove chunk2 uses the intermediate assertion to establish the final result
4. Compose using ensures_sequence
-/
theorem sequence_correct (pc a b c : ℕ) :
    ensures arm
      (sequence_pre pc a b c)
      (sequence_post pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) := by
  exact
   ensures_sequence
    (sequence_pre pc a b c)
    (sequence_mid pc a b)
    (sequence_post pc a b)
    (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3])
    (sequence_chunk1_correct pc a b c)
    (sequence_chunk2_correct pc a b)
    (maychange_regs_trans [Reg.PC, Reg.X1, Reg.X2, Reg.X3])


end Bignum.Arm.Tutorial
