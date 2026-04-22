/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Spec
public import Bignum.Arm.Machine
public import Bignum.Arm.Tactic
public import Bignum.Arm.Simulate
public import Bignum.Common.Word

@[expose] public section

/-!
# Sequence Example: Proving by Sequential Composition

This is a port of `s2n-bignum/arm/tutorial/sequence.ml`.

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

3. Prove each chunk with `ensures_of_exec`, compose with `ensures_sequence`.

## Simplification via `ensures_of_exec`

The original version used manual `eventually.ind` per instruction (~185 lines).
Using `ensures_of_exec`, we work directly with `exec chunk s₀`, reducing each
chunk proof to: decode + post + frame.
-/

namespace Bignum.Arm.Tutorial
open Bignum Bignum.Arm

/-!
## Machine Code
-/

def sequence_mc : List UInt8 :=
  [0x21, 0x00, 0x00, 0x8b,  -- ADD X1, X1, X0
   0x42, 0x00, 0x00, 0x8b,  -- ADD X2, X2, X0
   0x43, 0x00, 0x80, 0xd2,  -- MOV X3, #2
   0x21, 0x7c, 0x03, 0x9b]  -- MUL X1, X1, X3

/-- First chunk: two ADD instructions. -/
def chunk1_instrs : List Instruction :=
  [Instruction.ADD Reg.X1 Reg.X1 Reg.X0,
   Instruction.ADD Reg.X2 Reg.X2 Reg.X0]

/-- Second chunk: MOV + MUL. -/
def chunk2_instrs : List Instruction :=
  [Instruction.MOVZ Reg.X3 2 0,
   Instruction.MUL Reg.X1 Reg.X1 Reg.X3]

/-!
## Specification
-/

def sequence_pre (pc a b c : ℕ) (s : ArmState) : Prop :=
  aligned_bytes_loaded s.mem (BitVec.ofNat 64 pc) sequence_mc ∧
  s.read_reg Reg.PC = BitVec.ofNat 64 pc ∧
  s.read_reg Reg.X0 = BitVec.ofNat 64 a ∧
  s.read_reg Reg.X1 = BitVec.ofNat 64 b ∧
  s.read_reg Reg.X2 = BitVec.ofNat 64 c

/-- Intermediate assertion at pc+8: memory still loaded, PC at pc+8, X1 = a + b. -/
def sequence_mid (pc a b : ℕ) (s : ArmState) : Prop :=
  aligned_bytes_loaded s.mem (BitVec.ofNat 64 pc) sequence_mc ∧
  s.read_reg Reg.PC = BitVec.ofNat 64 (pc + 8) ∧
  s.read_reg Reg.X1 = BitVec.ofNat 64 (a + b)

def sequence_post (pc a b : ℕ) (s : ArmState) : Prop :=
  s.read_reg Reg.PC = BitVec.ofNat 64 (pc + 16) ∧
  s.read_reg Reg.X1 = BitVec.ofNat 64 ((a + b) * 2)

/-!
## Decode List Proofs

`arm_decode_list` proofs for each chunk, derived from `exec_at`.
-/

private theorem chunk1_decode_list (s : ArmState) (pc : Word64)
    (hb : bytes_loaded s.mem pc sequence_mc)
    (h_pc : s.read_reg Reg.PC = pc) :
    arm_decode_list chunk1_instrs s := by
  constructor
  · have key := exec_at s pc sequence_mc 0 hb (by decide)
                  (Instruction.ADD Reg.X1 Reg.X1 Reg.X0) (by decide)
    rwa [show pc + BitVec.ofNat 64 0 = pc from by bv_omega, ← h_pc] at key
  constructor
  · let s₁ := step (Instruction.ADD Reg.X1 Reg.X1 Reg.X0) s
    have h_mem1 : s₁.mem = s.mem := by simp [step, advance_pc, ArmState.write_reg, s₁]
    have h_pc1 : s₁.read_reg Reg.PC = pc + 4 := by
      simp only [ArmState.read_reg, step, advance_pc, ArmState.write_reg, BitVec.ofNat_eq_ofNat,
        ↓reduceIte, BitVec.add_left_inj, s₁]
      rw [← ArmState.read_reg, h_pc]
    have hb' : bytes_loaded s₁.mem pc sequence_mc := h_mem1 ▸ hb
    have key := exec_at s₁ pc sequence_mc 4 hb' (by decide)
                  (Instruction.ADD Reg.X2 Reg.X2 Reg.X0) (by decide)
    rwa [show pc + BitVec.ofNat 64 4 = pc + 4 from by bv_omega, ← h_pc1] at key
  · trivial

private theorem chunk2_decode_list (s : ArmState) (pc : Word64)
    (hb : bytes_loaded s.mem pc sequence_mc)
    (h_pc : s.read_reg Reg.PC = pc + 8) :
    arm_decode_list chunk2_instrs s := by
  constructor
  · have key := exec_at s pc sequence_mc 8 hb (by decide)
                  (Instruction.MOVZ Reg.X3 2 0) (by decide)
    rwa [show pc + BitVec.ofNat 64 8 = pc + 8 from by bv_omega, ← h_pc] at key
  constructor
  · let s₁ := step (Instruction.MOVZ Reg.X3 2 0) s
    have h_mem1 : s₁.mem = s.mem := by simp [step, advance_pc, ArmState.write_reg, s₁]
    have h_pc1 : s₁.read_reg Reg.PC = pc + 12 := by
      simp only [ArmState.read_reg, step, advance_pc, ArmState.write_reg, BitVec.ofNat_eq_ofNat,
        pow_zero, mul_one, ↓reduceIte, s₁]
      rw [← ArmState.read_reg, h_pc]
      bv_omega
    have hb' : bytes_loaded s₁.mem pc sequence_mc := h_mem1 ▸ hb
    have key := exec_at s₁ pc sequence_mc 12 hb' (by decide)
                  (Instruction.MUL Reg.X1 Reg.X1 Reg.X3) (by decide)
    rwa [show pc + BitVec.ofNat 64 12 = pc + 12 from by bv_omega, ← h_pc1] at key
  · trivial


/-!
## Chunk Proofs
-/

/-- First chunk: two ADD instructions, PC advances from pc to pc+8. -/
theorem sequence_chunk1_correct (pc a b c : ℕ) :
    ensures arm
      (sequence_pre pc a b c)
      (sequence_mid pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) := by
  apply ensures_of_exec chunk1_instrs
  · intro s ⟨h_loaded, h_pc, _, _, _⟩
    exact chunk1_decode_list s _ h_loaded.2 h_pc
  · -- Post: sequence_mid
    intro s ⟨h_loaded, h_pc, h_x0, h_x1, h_x2⟩
    simp only [sequence_mid, exec, chunk1_instrs, List.foldl,
               step, advance_pc, ArmState.write_reg, ArmState.read_reg]
    rw [show s.regs Reg.PC = BitVec.ofNat 64 pc from h_pc]
    rw [show s.regs Reg.X0 = BitVec.ofNat 64 a from h_x0]
    rw [show s.regs Reg.X1 = BitVec.ofNat 64 b from h_x1]
    simp only [Reg.X1, Reg.X2, Reg.X0, if_true]
    constructor
    · assumption
    · constructor
      · bv_omega
      · simp only [Fin.isValue, reduceCtorEq, ↓reduceIte, Reg.X.injEq, Fin.reduceEq]
        bv_omega
  · -- Frame
    intro s _ r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    obtain ⟨hne_pc, hne_x1, hne_x2, hne_x3⟩ := hr
    simp only [unchanged_reg, exec, chunk1_instrs, List.foldl,
               step, advance_pc, ArmState.write_reg, ArmState.read_reg]
    simp [hne_pc, hne_x1, hne_x2]

/-- Second chunk: MOV + MUL, PC advances from pc+8 to pc+16. -/
theorem sequence_chunk2_correct (pc a b : ℕ) :
    ensures arm
      (sequence_mid pc a b)
      (sequence_post pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) := by
  apply ensures_of_exec chunk2_instrs
  · intro s ⟨h_loaded, h_pc, _⟩
    have h_pc' : s.read_reg Reg.PC = BitVec.ofNat 64 pc + 8 := by
      rw [h_pc]; simp [← BitVec.ofNat_add_ofNat]
    exact chunk2_decode_list s _ h_loaded.2 h_pc'
  · -- Post: sequence_post
    intro s ⟨_, h_pc, h_x1⟩
    simp only [sequence_post, exec, chunk2_instrs, List.foldl,
               step, advance_pc, ArmState.write_reg, ArmState.read_reg]
    have h_pc' : s.regs Reg.PC = BitVec.ofNat 64 pc + 8 := by
      rw [← ArmState.read_reg, h_pc]; simp [← BitVec.ofNat_add_ofNat]
    rw [h_pc']
    rw [show s.regs Reg.X1 = BitVec.ofNat 64 (a + b) from h_x1]
    simp only [show Reg.X3 = Reg.PC ↔ False from by decide,
               show Reg.PC = Reg.X3 ↔ False from by decide,
               show Reg.X1 = Reg.PC ↔ False from by decide,
               show Reg.PC = Reg.X1 ↔ False from by decide,
               show Reg.X1 = Reg.X3 ↔ False from by decide,
               if_false, if_true]
    constructor
    · bv_omega
    · simp [← BitVec.ofNat_mul_ofNat]
  · -- Frame
    intro s _ r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    obtain ⟨hne_pc, hne_x1, _, hne_x3⟩ := hr
    simp only [unchanged_reg, exec, chunk2_instrs, List.foldl,
               step, advance_pc, ArmState.write_reg, ArmState.read_reg]
    simp [hne_pc, hne_x1, hne_x3]


/-!
## Compositional Verification
-/

/--
Sequential composition: chain two `ensures` with the same frame when the frame
is transitive. Corresponds to HOL Light's `ENSURES_SEQUENCE_TAC`.
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
  exact eventually_mono (fun s₂ hpf =>
    ⟨hpf.1, h_frame_trans s₀ s₁ s₂ h_f1 hpf.2⟩) s₁ h_ev2

theorem maychange_regs_trans (regs : List Reg) :
    ∀ s1 s2 s3, maychange_regs regs s1 s2 →
                maychange_regs regs s2 s3 →
                maychange_regs regs s1 s3 := by
  intro s1 s2 s3 h12 h23
  unfold maychange_regs unchanged_reg at *
  intro r hr; rw [h12 r hr, h23 r hr]


/-!
## Main Correctness Theorem
-/

theorem sequence_correct (pc a b c : ℕ) :
    ensures arm
      (sequence_pre pc a b c)
      (sequence_post pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) :=
  ensures_sequence _ _ _
    (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3])
    (sequence_chunk1_correct pc a b c)
    (sequence_chunk2_correct pc a b)
    (maychange_regs_trans _)

end Bignum.Arm.Tutorial
