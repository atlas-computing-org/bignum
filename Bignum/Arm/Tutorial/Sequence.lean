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

/--
Length of the sequence program machine code.
-/
theorem sequence_mc_length : sequence_mc.length = 16 := by rfl

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

Source: s2n-bignum/arm/tutorial/sequence.ml:51-64
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
  sorry

/-- Decode instruction 2: ADD X2, X2, X0 -/
theorem sequence_decode_instr2 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s (pc + 4) = some (Instruction.ADD Reg.X2 Reg.X2 Reg.X0) := by
  sorry

/-- Decode instruction 3: MOV X3, #2 (encoded as MOVZ) -/
theorem sequence_decode_instr3 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s (pc + 8) = some (Instruction.MOVZ Reg.X3 2 0) := by
  sorry

/-- Decode instruction 4: MUL X1, X1, X3 -/
theorem sequence_decode_instr4 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc sequence_mc) :
    arm_decode s (pc + 12) = some (Instruction.MUL Reg.X1 Reg.X1 Reg.X3) := by
  sorry

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
  sorry

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
  sorry

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

Source: s2n-bignum/arm/tutorial/sequence.ml
-/
theorem sequence_correct (pc a b c : ℕ) :
    ensures arm
      (sequence_pre pc a b c)
      (sequence_post pc a b)
      (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3]) :=
  ensures_sequence
    (sequence_pre pc a b c)
    (sequence_mid pc a b)
    (sequence_post pc a b)
    (maychange_regs [Reg.PC, Reg.X1, Reg.X2, Reg.X3])
    (sequence_chunk1_correct pc a b c)
    (sequence_chunk2_correct pc a b)
    (maychange_regs_trans [Reg.PC, Reg.X1, Reg.X2, Reg.X3])

end Bignum.Arm.Tutorial
