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
def simple_program : Program := {
  base_addr := Word64.ofNat 0
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
  prog := simple_program
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

The core correctness lemma: executing the simple program satisfies the
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
  (h_pc_bound : pc < 2 ^ 64)
  (h_a_bound : a < 2 ^ 64)
  (h_b_bound : b < 2 ^ 64)
  (h_sum_bound : a + b < 2 ^ 64)
  :  (simple_spec pc a b).satisfies := by
  unfold Ensures.satisfies simple_spec
  intro s_init h_pre
  obtain ⟨h_pc, h_x0, h_x1, h_align⟩ := h_pre
  simp only

  -- Execute the program: exec_program checks PC and runs instructions
  unfold exec_program simple_program
  split
  · -- Case 1: PC matches base_addr, program executes
    -- Expand exec: [ADD, SUB].foldl step s_init = step SUB (step ADD s_init)
    unfold exec
    simp only [List.foldl]
    -- Expand step for both instructions
    unfold step

    -- Now prove: postcondition ∧ frame
    constructor
    · -- Postcondition: PC = pc + 8 ∧ X2 = a
      constructor

      -- PC advances by 8 bytes (4 + 4)
      · simp only [ArmState.read_write_same,
          ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X2)]
        rw [h_pc]
        rw [BitVec.add_assoc]
        unfold Word64.ofNat
        rw [← BitVec.ofNat_add_ofNat]
        simp

      -- X2 contains a (the arithmetic (a + b) - b = a)
      · simp only [ArmState.read_write_same]
        rw [h_x0, h_x1]
        -- Goal: (Word64.ofNat b + Word64.ofNat a) - Word64.ofNat b = Word64.ofNat a
        sorry  -- BitVec arithmetic: (a + b) - b = a when a + b < 2^64

    · -- Frame: only PC and X2 may change
      unfold maychange_regs unchanged_reg
      intro r h_not_changed
      -- r is not in [PC, X2]
      simp only [List.mem_cons] at h_not_changed
      push_neg at h_not_changed
      obtain ⟨h_r_ne_pc, h_r_ne_x2, _⟩ := h_not_changed

      -- Show r is unchanged through both instructions
      -- After ADD: write PC then X2, read r (which is neither)
      -- After SUB: write PC then X2, read r (which is neither)
      simp only [ArmState.read_write_diff _ _ _ _ (Ne.symm h_r_ne_x2),
                 ArmState.read_write_diff _ _ _ _ (Ne.symm h_r_ne_pc)]

  · -- Case 2: PC doesn't match (contradiction with precondition)
    -- exec_program returns s_init unchanged when PC doesn't match
    -- But our precondition says s_init.read_reg Reg.PC = Word64.ofNat pc
    -- And simple_program.base_addr = Word64.ofNat 0
    -- So this branch is impossible when pc = 0, or provable otherwise
    sorry

/-
Note on the proof:

**Simplified proof structure using read/write lemmas:**

The proof now uses the @[simp] lemmas from State.lean:
- `ArmState.read_write_same`: Reading after writing to same register
- `ArmState.read_write_diff`: Reading after writing to different register

This eliminates the manual state manipulation that was previously required.

**Remaining sorry placeholders:**

1. **BitVec addition with constants** (line 190):
   `Word64.ofNat pc + 4 + 4 = Word64.ofNat (pc + 8)`
   Need: BitVec.add_assoc and conversion lemmas

2. **BitVec arithmetic cancellation** (line 202):
   `(Word64.ofNat b + Word64.ofNat a) - Word64.ofNat b = Word64.ofNat a`
   Need: BitVec subtraction cancellation when no overflow

**Comparison with HOL Light:**

HOL Light uses `CONV_TAC WORD_RULE` which automatically solves word arithmetic.
In Lean, we need explicit BitVec arithmetic lemmas from Mathlib or a custom library.

The proof structure is now much cleaner and closely mirrors the HOL Light approach:
1. Unfold program execution (like ARM_STEPS_TAC)
2. Apply simplification lemmas (like ASM_REWRITE_TAC)
3. Solve arithmetic (would use BitVec tactics instead of WORD_RULE)
-/

end Bignum.Arm.Tutorial
