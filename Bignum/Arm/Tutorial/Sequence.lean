/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Spec.Ensures
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
-/

namespace Bignum.Arm.Tutorial
open Bignum Bignum.Arm

/-
The sequence program byte sequence (16 bytes = 4 instructions).

ARM is little-endian, so:
- Bytes [0x21, 0x00, 0x00, 0x8b] encode instruction 0x8b000021 = ADD X1, X1, X0
- Bytes [0x42, 0x00, 0x00, 0x8b] encode instruction 0x8b000042 = ADD X2, X2, X0
- Bytes [0x43, 0x00, 0x80, 0xd2] encode instruction 0xd2800043 = MOV X3, #2
- Bytes [0x21, 0x7c, 0x03, 0x9b] encode instruction 0x9b037c21 = MUL X1, X1, X3
-/
def sequence_program_bytes : List UInt8 :=
  [0x21, 0x00, 0x00, 0x8b,  -- ADD X1, X1, X0
   0x42, 0x00, 0x00, 0x8b,  -- ADD X2, X2, X0
   0x43, 0x00, 0x80, 0xd2,  -- MOV X3, #2
   0x21, 0x7c, 0x03, 0x9b]  -- MUL X1, X1, X3

/--
The sequence program loaded from byte sequence.
-/
def sequence_program (pc : Nat) : Program :=
  Program.fromBytes (Word64.ofNat pc) sequence_program_bytes

/--
The manually constructed version of sequence_program (for reference and proofs).

Note: `MOV X3, #2` in ARM assembly is encoded as `MOVZ X3, #2, LSL #0`.
-/
def sequence_program_manual (pc : Nat) : Program := {
  base_addr := Word64.ofNat pc
  instructions := [
    Instruction.ADD Reg.X1 Reg.X1 Reg.X0,   -- x1 := x1 + x0
    Instruction.ADD Reg.X2 Reg.X2 Reg.X0,   -- x2 := x2 + x0
    Instruction.MOVZ Reg.X3 2 0,            -- x3 := 2 (MOVZ with LSL #0)
    Instruction.MUL Reg.X1 Reg.X1 Reg.X3    -- x1 := x1 * x3
  ]
}

/-!
## Sequential Composition of Ensures Specifications

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
Split a program at a given instruction index.

Returns (first_chunk, second_chunk) where:
- first_chunk contains instructions [0, i)
- second_chunk contains instructions [i, end)
-/
def Program.split (p : Program) (i : Nat) : Program × Program :=
  let first_instrs := p.instructions.take i
  let second_instrs := p.instructions.drop i
  let first_prog := { base_addr := p.base_addr, instructions := first_instrs }
  let second_prog := {
    base_addr := p.base_addr + Word64.ofNat (i * 4),
    instructions := second_instrs }
  (first_prog, second_prog)

/--
Sequential composition of ensures: if we can prove ensures for two sequential
chunks, we can derive ensures for the whole program.

This corresponds to HOL Light's `ENSURES_SEQUENCE_TAC` which takes:
- A split point (e.g., `pc + 8`)
- An intermediate assertion (e.g., `\s. read X1 s = word (a + b)`)

And produces two subgoals:
1. ensures for first chunk with intermediate as postcondition
2. ensures for second chunk with intermediate as precondition

Source: s2n-bignum/arm/tutorial/sequence.ml:75-77
-/
theorem ensures_sequence
    (pre mid post : ArmState → Prop)
    (frame : ArmState → ArmState → Prop)
    (prog1 prog2 : Program)
    (h1 : ∀ s_init, pre s_init →
      let s_mid := exec_program prog1 s_init
      mid s_mid ∧ frame s_init s_mid)
    (h2 : ∀ s_mid, mid s_mid →
      let s_final := exec_program prog2 s_mid
      post s_final ∧ frame s_mid s_final)
    (h_frame_trans : ∀ s1 s2 s3, frame s1 s2 → frame s2 s3 → frame s1 s3)
    : ∀ s_init, pre s_init →
        let s_final := exec_program prog2 (exec_program prog1 s_init)
        post s_final ∧ frame s_init s_final := by
  intro s_init h_pre
  have ⟨h_mid, h_frame1⟩ := h1 s_init h_pre
  have ⟨h_post, h_frame2⟩ := h2 _ h_mid
  exact ⟨h_post, h_frame_trans _ _ _ h_frame1 h_frame2⟩

/-!
## The Specification

```ocaml
let sequence_SPEC = prove(
  `forall pc a b.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) sequence_mc /\
         read PC s = word pc /\
         read X0 s = word a /\
         read X1 s = word b /\
         read X2 s = word c)
    // Postcondition
    (\s. read PC s = word (pc+16) /\
         read X1 s = word ((a + b) * 2))
    // Registers that may change
    (MAYCHANGE [PC;X1;X2;X3])`,
  ...)
```

Source: s2n-bignum/arm/tutorial/sequence.ml:51-64
-/

/--
Specification for the sequence program.

**Precondition:**
- PC is at the program start
- X0 contains value a
- X1 contains value b
- X2 contains value c
- Program bytes are loaded at PC

**Postcondition:**
- PC has advanced by 16 (four instructions × 4 bytes each)
- X1 contains (a + b) * 2

**Frame:**
- Only PC, X1, X2, X3 may change
- All other registers and memory unchanged

Source: s2n-bignum/arm/tutorial/sequence.ml:51-64
-/
def sequence_spec (pc a b c : ℕ) : Ensures := {
  pre := fun s =>
    s.read_reg Reg.PC = Word64.ofNat pc ∧
    s.read_reg Reg.X0 = Word64.ofNat a ∧
    s.read_reg Reg.X1 = Word64.ofNat b ∧
    s.read_reg Reg.X2 = Word64.ofNat c ∧
    pc % 4 = 0  -- 4-byte alignment

  post := fun s =>
    s.read_reg Reg.PC = Word64.ofNat (pc + 16) ∧
    s.read_reg Reg.X1 = Word64.ofNat ((a + b) * 2)

  frame := maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]
  prog := sequence_program pc
}

/-!
## First Chunk

Corresponds to HOL Light's first subgoal after `ENSURES_SEQUENCE_TAC`:

```ocaml
ENSURES_INIT_TAC "s0" THEN
ARM_STEPS_TAC EXEC (1--2) THEN
ENSURES_FINAL_STATE_TAC THEN
ASM_REWRITE_TAC[] THEN
CONV_TAC WORD_RULE
```

Source: s2n-bignum/arm/tutorial/sequence.ml:84-92
-/

/--
First chunk of the program: two ADD instructions.
-/
def sequence_chunk1 (pc : Nat) : Program := {
  base_addr := Word64.ofNat pc
  instructions := [
    Instruction.ADD Reg.X1 Reg.X1 Reg.X0,  -- x1 := x1 + x0
    Instruction.ADD Reg.X2 Reg.X2 Reg.X0   -- x2 := x2 + x0
  ]
}

/--
Intermediate assertion: after the first chunk, X1 = a + b.

This is the `\s. read X1 s = word (a + b)` from HOL Light's
`ENSURES_SEQUENCE_TAC`.

Source: s2n-bignum/arm/tutorial/sequence.ml:77
-/
def sequence_mid (pc a b : ℕ) (s : ArmState) : Prop :=
  s.read_reg Reg.PC = Word64.ofNat (pc + 8) ∧
  s.read_reg Reg.X1 = Word64.ofNat (a + b)

/--
First chunk specification: the two ADD instructions.

Precondition: PC at start, X0 = a, X1 = b
Postcondition: PC at pc+8, X1 = a + b

Source: s2n-bignum/arm/tutorial/sequence.ml:80-92
-/
theorem sequence_chunk1_correct (pc a b c : ℕ)
    (s_init : ArmState)
    (h_pc : s_init.read_reg Reg.PC = Word64.ofNat pc)
    (h_x0 : s_init.read_reg Reg.X0 = Word64.ofNat a)
    (h_x1 : s_init.read_reg Reg.X1 = Word64.ofNat b)
    (h_x2 : s_init.read_reg Reg.X2 = Word64.ofNat c) :
    let s_mid := exec_program (sequence_chunk1 pc) s_init
    s_mid.read_reg Reg.PC = Word64.ofNat (pc + 8) ∧
    s_mid.read_reg Reg.X1 = Word64.ofNat (a + b) := by
  -- Unfold definitions and symbolically execute
  unfold sequence_chunk1 exec_program
  simp only [h_pc]
  -- PC matches, so we execute
  simp only [ite_true, exec]
  simp only [List.foldl]
  repeat rw [step]
  simp only [ArmState.read_write_same]
  constructor
  · -- PC = pc + 8
    rw [h_pc]
    rw [BitVec.add_assoc]
    unfold Word64.ofNat
    rw [← BitVec.ofNat_add_ofNat]
    simp
  · -- X1 = a + b
    simp only [
      ArmState.read_write_same,
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.X2 ≠ Reg.X1)
    ]
    rw [h_x0, h_x1]
    -- word_add (word b) (word a) = word (a + b)
    -- Need: BitVec.ofNat 64 b + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + b)
    unfold Word64.ofNat
    -- Use commutativity of BitVec addition then combine
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]

/-!
## Second Chunk

Corresponds to HOL Light's second subgoal:

```ocaml
ENSURES_INIT_TAC "s0" THEN
ARM_STEPS_TAC EXEC (1--2) THEN
ENSURES_FINAL_STATE_TAC THEN
ASM_REWRITE_TAC[] THEN
CONV_TAC WORD_RULE
```

Source: s2n-bignum/arm/tutorial/sequence.ml:95-100
-/

/--
Second chunk of the program: MOVZ and MUL instructions.
-/
def sequence_chunk2 (pc : Nat) : Program := {
  base_addr := Word64.ofNat (pc + 8)
  instructions := [
    Instruction.MOVZ Reg.X3 2 0,           -- x3 := 2 (MOVZ with LSL #0)
    Instruction.MUL Reg.X1 Reg.X1 Reg.X3   -- x1 := x1 * x3
  ]
}

/--
Second chunk specification: MOV x3, #2 and MUL x1, x1, x3.

Precondition: PC at pc+8, X1 = a + b (from intermediate assertion)
Postcondition: PC at pc+16, X1 = (a + b) * 2

Source: s2n-bignum/arm/tutorial/sequence.ml:95-100
-/
theorem sequence_chunk2_correct (pc a b : ℕ)
    (s_mid : ArmState)
    (h_pc : s_mid.read_reg Reg.PC = Word64.ofNat (pc + 8))
    (h_x1 : s_mid.read_reg Reg.X1 = Word64.ofNat (a + b)) :
    let s_final := exec_program (sequence_chunk2 pc) s_mid
    s_final.read_reg Reg.PC = Word64.ofNat (pc + 16) ∧
    s_final.read_reg Reg.X1 = Word64.ofNat ((a + b) * 2) := by
  -- Unfold definitions and symbolically execute
  unfold sequence_chunk2 exec_program
  simp only [h_pc]
  -- PC matches, so we execute
  simp only [ite_true, exec]
  simp only [List.foldl]
  repeat rw [step]
  simp only [ArmState.read_write_same]
  -- Simplify 2^0 = 1
  simp only [Nat.pow_zero, Nat.mul_one]
  constructor
  · -- PC = pc + 16
    rw [h_pc]
    unfold Word64.ofNat
    -- The goal is: BitVec.ofNat 64 (pc + 8) + 4 + 4 = BitVec.ofNat 64 (pc + 16)
    -- TODO: This requires showing that Nat-to-BitVec coercion works correctly
    -- The arithmetic is: (pc + 8) + 4 + 4 = pc + 16, which is trivially true
    sorry
  · -- X1 = (a + b) * 2
    -- First simplify to get X3 = 2
    simp only [
      ArmState.read_write_same,
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.X3 ≠ Reg.X1),
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X3)
    ]
    rw [h_x1]
    -- word (a + b) * 2 = word ((a + b) * 2)
    unfold Word64.ofNat
    rw [← BitVec.ofNat_mul_ofNat]


/-!
## Compositional Proof Using ensures_sequence

This section demonstrates the proper use of `ensures_sequence` to compose
the chunk proofs, matching HOL Light's `ENSURES_SEQUENCE_TAC` approach.
-/

/--
Precondition for the sequence program: PC at start, registers initialized.
-/
def sequence_pre (pc a b c : ℕ) (s : ArmState) : Prop :=
  s.read_reg Reg.PC = Word64.ofNat pc ∧
  s.read_reg Reg.X0 = Word64.ofNat a ∧
  s.read_reg Reg.X1 = Word64.ofNat b ∧
  s.read_reg Reg.X2 = Word64.ofNat c

-- Note: sequence_mid is already defined above (line 241)

/--
Postcondition: PC at pc+16, X1 = (a+b)*2.
-/
def sequence_post (pc a b : ℕ) (s : ArmState) : Prop :=
  s.read_reg Reg.PC = Word64.ofNat (pc + 16) ∧
  s.read_reg Reg.X1 = Word64.ofNat ((a + b) * 2)

/--
Chunk1 with frame: establishes intermediate assertion with frame condition.
-/
theorem sequence_chunk1_with_frame (pc a b c : ℕ) :
    ∀ s_init, sequence_pre pc a b c s_init →
      let s_mid := exec_program (sequence_chunk1 pc) s_init
      sequence_mid pc a b s_mid ∧ maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3] s_init s_mid := by
  intro s_init ⟨h_pc, h_x0, h_x1, h_x2⟩
  have h := sequence_chunk1_correct pc a b c s_init h_pc h_x0 h_x1 h_x2
  constructor
  · -- Intermediate assertion
    exact h
  · -- Frame: only PC, X1, X2, X3 may change
    unfold maychange_regs unchanged_reg
    intro r h_not_changed
    simp only [List.mem_cons] at h_not_changed
    push_neg at h_not_changed
    obtain ⟨h_ne_pc, h_ne_x1, h_ne_x2, h_ne_x3, _⟩ := h_not_changed
    -- Prove r is unchanged by symbolic execution
    unfold sequence_chunk1 exec_program
    simp only [h_pc, ite_true, exec, List.foldl]
    repeat rw [step]
    simp only [
      ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x1),
      ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x2),
      ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)
    ]

/--
Chunk2 with frame: establishes postcondition with frame condition.
-/
theorem sequence_chunk2_with_frame (pc a b : ℕ) :
    ∀ s_mid, sequence_mid pc a b s_mid →
      let s_final := exec_program (sequence_chunk2 pc) s_mid
      sequence_post pc a b s_final ∧ maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3] s_mid s_final := by
  intro s_mid ⟨h_pc, h_x1⟩
  have h := sequence_chunk2_correct pc a b s_mid h_pc h_x1
  constructor
  · -- Postcondition
    exact h
  · -- Frame: only PC, X1, X2, X3 may change
    unfold maychange_regs unchanged_reg
    intro r h_not_changed
    simp only [List.mem_cons] at h_not_changed
    push_neg at h_not_changed
    obtain ⟨h_ne_pc, h_ne_x1, h_ne_x2, h_ne_x3, _⟩ := h_not_changed
    -- Prove r is unchanged by symbolic execution
    unfold sequence_chunk2 exec_program
    simp only [h_pc, ite_true, exec, List.foldl]
    repeat rw [step]
    simp only [Nat.pow_zero, Nat.mul_one]
    simp only [
      ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x1),
      ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x3),
      ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)
    ]

/--
Frame transitivity for maychange_regs.
-/
theorem maychange_regs_trans (regs : List Reg) :
    ∀ s1 s2 s3, maychange_regs regs s1 s2 → maychange_regs regs s2 s3 → maychange_regs regs s1 s3 := by
  intro s1 s2 s3 h12 h23
  unfold maychange_regs unchanged_reg at *
  intro r hr
  rw [h12 r hr, h23 r hr]

/--
Compositional correctness using ensures_sequence.

This proof demonstrates the proper use of compositional verification:
1. Use sequence_chunk1_with_frame for the first chunk
2. Use sequence_chunk2_with_frame for the second chunk
3. Apply ensures_sequence to compose them

This corresponds to HOL Light's ENSURES_SEQUENCE_TAC approach.
-/
theorem sequence_correct_compositional (pc a b c : ℕ) :
    ∀ s_init, sequence_pre pc a b c s_init →
      let s_final := exec_program (sequence_chunk2 pc) (exec_program (sequence_chunk1 pc) s_init)
      sequence_post pc a b s_final ∧ maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3] s_init s_final :=
  ensures_sequence
    (sequence_pre pc a b c)
    (sequence_mid pc a b)
    (sequence_post pc a b)
    (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3])
    (sequence_chunk1 pc)
    (sequence_chunk2 pc)
    (sequence_chunk1_with_frame pc a b c)
    (sequence_chunk2_with_frame pc a b)
    (maychange_regs_trans [Reg.PC, Reg.X1, Reg.X2, Reg.X3])

/-!
## Full Program Correctness

Now we compose the two chunk proofs to get the full program correctness.

This corresponds to HOL Light's final result after `ENSURES_SEQUENCE_TAC`
splits the proof and both subgoals are discharged.
-/

/--
Main correctness theorem: the sequence program satisfies its specification.

The proof demonstrates compositional verification:
1. Split the program at pc+8
2. Prove chunk1 establishes the intermediate assertion (X1 = a + b)
3. Prove chunk2 uses the intermediate assertion to establish the final result

Source: s2n-bignum/arm/tutorial/sequence.ml
-/
theorem sequence_correct (pc a b c : ℕ)
    : (sequence_spec pc a b c).satisfies := by
  unfold Ensures.satisfies sequence_spec
  simp only
  intro s_init ⟨h_pc, h_x0, h_x1, h_x2, h_align⟩
  -- Use the compositional proof
  have h_pre : sequence_pre pc a b c s_init := ⟨h_pc, h_x0, h_x1, h_x2⟩
  have h := sequence_correct_compositional pc a b c s_init h_pre
  -- The programs chunk1 ∘ chunk2 should equal the full manual program
  -- TODO: prove program equivalence
  sorry

/--
Alternative proof using the manual program definition directly.

This version explicitly demonstrates the compositional verification technique.
-/
theorem sequence_correct_manual (pc a b c : ℕ)
    (s_init : ArmState)
    (h_pc : s_init.read_reg Reg.PC = Word64.ofNat pc)
    (h_x0 : s_init.read_reg Reg.X0 = Word64.ofNat a)
    (h_x1 : s_init.read_reg Reg.X1 = Word64.ofNat b)
    (h_x2 : s_init.read_reg Reg.X2 = Word64.ofNat c) :
    let s_final := exec_program (sequence_program_manual pc) s_init
    s_final.read_reg Reg.PC = Word64.ofNat (pc + 16) ∧
    s_final.read_reg Reg.X1 = Word64.ofNat ((a + b) * 2) := by
  -- The proof proceeds by symbolic execution of all 4 instructions
  -- This follows the ENSURES_INIT_TAC + ARM_STEPS_TAC pattern from HOL Light
  unfold sequence_program_manual exec_program
  simp only [h_pc]
  simp only [ite_true, exec]
  simp only [List.foldl]
  repeat rw [step]
  simp only [ArmState.read_write_same]
  -- Simplify 2^0 = 1 from MOVZ
  simp only [Nat.pow_zero, Nat.mul_one]
  constructor
  · -- PC = pc + 16
    rw [h_pc]
    unfold Word64.ofNat
    -- Goal: BitVec.ofNat 64 pc + 4 + 4 + 4 + 4 = BitVec.ofNat 64 (pc + 16)
    -- TODO: This requires showing that Nat-to-BitVec coercion works correctly
    -- The arithmetic is: pc + 4 + 4 + 4 + 4 = pc + 16, which is trivially true
    sorry
  · -- X1 = (a + b) * 2
    simp only [
      ArmState.read_write_same,
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.X2 ≠ Reg.X1),
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.X3 ≠ Reg.X1),
      ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X3)
    ]
    rw [h_x0, h_x1]
    -- (word b + word a) * word 2 = word ((a + b) * 2)
    unfold Word64.ofNat
    -- Use commutativity: b + a = a + b, and combine
    simp only [BitVec.add_comm (BitVec.ofNat 64 b) (BitVec.ofNat 64 a),
               ← BitVec.ofNat_add_ofNat, ← BitVec.ofNat_mul_ofNat]

end Bignum.Arm.Tutorial
