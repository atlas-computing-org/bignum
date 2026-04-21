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

Port of `s2n-bignum/arm/tutorial/simple.ml`.

The program is two instructions:

```asm
0:   8b000022        add     x2, x1, x0
4:   cb010042        sub     x2, x2, x1
```

Starting with `X0 = a` and `X1 = b`, after executing both instructions we have
`X2 = a`.

Source: s2n-bignum/arm/tutorial/simple.ml
-/

namespace Bignum.Arm.Tutorial
open Bignum Bignum.Arm

/-!
## Machine Code

Corresponds to HOL Light:
```ocaml
let simple_mc = new_definition `simple_mc = [
    word 0x22; word 0x00; word 0x00; word 0x8b; // add x2, x1, x0
    word 0x42; word 0x00; word 0x01; word 0xcb  // sub x2, x2, x1
  ]:((8)word)list`;;
```
-/

def simple_mc : List UInt8 :=
  [0x22, 0x00, 0x00, 0x8b,  -- add x2, x1, x0
   0x42, 0x00, 0x01, 0xcb]  -- sub x2, x2, x1

/-!
## Loading Bytes from an Object File

HOL Light offers an alternative to writing the byte list by hand — reading it
directly from the compiled `.o` file.

The Lean equivalent is provided by `Bignum.Arm.Machine.Loader` (already imported
transitively through `Bignum.Arm.Spec`).

### Discovering bytes at elaboration time (`#load_obj`)

The `#load_obj` command runs at elaboration time and prints the byte list in a
form ready to paste into a `def`:

```lean
#load_obj "s2n-bignum/arm/tutorial/simple.o"
-- Output: 8 bytes from simple.o
-- [ 0x22, 0x00, 0x00, 0x8b,
--   0x42, 0x00, 0x01, 0xcb, ]
```

This is the direct analogue of `print_literal_from_elf`.

### Verifying bytes at run time (`#eval assertTextSectionFromObj`)

`define_assert_from_elf` also *asserts* that the file matches the proof-level
list. The Lean equivalent is:

```lean
#eval assertTextSectionFromObj "s2n-bignum/arm/tutorial/simple.o" simple_mc
-- [Loader] …/simple.o: OK (8 bytes verified)
```

This checks that the bytes the assembler produced match the `simple_mc` list
used in the proof, keeping the TCB honest without adding the file to the TCB.

### Loading a `Program` directly

```lean
-- Load + decode into a Program (no verification)
def simple_program : IO Program :=
  Program.fromObj 0 "s2n-bignum/arm/tutorial/simple.o"

-- Load + verify + decode (throws if bytes differ)
def simple_program_verified : IO Program :=
  Program.fromObjVerified 0 "s2n-bignum/arm/tutorial/simple.o" simple_mc
```

### Design note: loader is outside the TCB

The `simple_mc` byte list in this file is the **ground truth** of the trusted
computing base. The loader (`Loader.lean`) lives entirely outside the TCB: it
provides a convenient way to check that the assembler produced the expected
bytes, but the proof of `SIMPLE_SPEC` only depends on `simple_mc` as defined
above, never on any file-system read.
-/


/-!
## EXEC

`ARM_MK_EXEC_RULE simple_mc` in HOL Light pre-computes a decode theorem for each
instruction offset. Here we prove the two decode facts directly.

Corresponds to:
```ocaml
let EXEC = ARM_MK_EXEC_RULE simple_mc;;
```
-/

/-- Decode result at offset 0: ADD X2, X1, X0. -/
theorem EXEC_0 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc simple_mc) :
    arm_decode s pc = some (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) := by
  obtain ⟨_h₁, hb⟩ := h
  have key := exec_at s pc simple_mc 0 hb (by decide)
                (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) (by decide)
  rwa [show pc + BitVec.ofNat 64 0 = pc from by bv_omega] at key

/-- Decode result at offset 4: SUB X2, X2, X1. -/
theorem EXEC_4 (s : ArmState) (pc : Word64)
    (h : aligned_bytes_loaded s.mem pc simple_mc) :
    arm_decode s (pc + 4) = some (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) := by
  obtain ⟨_h₁, hb⟩ := h
  have key := exec_at s pc simple_mc 4 hb (by decide)
                (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) (by decide)
  rwa [show pc + BitVec.ofNat 64 4 = pc + 4 from by bv_omega] at key


/-!
## SIMPLE_SPEC

Corresponds to HOL Light:
```ocaml
let SIMPLE_SPEC = prove(
  `forall pc a b.
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) simple_mc /\
         read PC s = word pc /\
         read X0 s = word a /\
         read X1 s = word b)
    (\s. read PC s = word (pc+8) /\
         read X2 s = word a)
    (MAYCHANGE [PC;X2])`, ...);;
```
-/

theorem SIMPLE_SPEC (pc a b : ℕ) :
    ensures arm
      (fun s => aligned_bytes_loaded s.mem (BitVec.ofNat 64 pc) simple_mc ∧
                s.read_reg Reg.PC = BitVec.ofNat 64 pc ∧
                s.read_reg Reg.X0 = BitVec.ofNat 64 a ∧
                s.read_reg Reg.X1 = BitVec.ofNat 64 b)
      (fun s => s.read_reg Reg.PC = BitVec.ofNat 64 (pc + 8) ∧
                s.read_reg Reg.X2 = BitVec.ofNat 64 a)
      (maychange_regs [Reg.PC, Reg.X2]) := by
  intro s₀ ⟨h_loaded, h_pc, h_x0, h_x1⟩
  -- Step s0 → s1: execute ADD X2, X1, X0
  apply eventually.ind
  · exact ⟨step (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) s₀,
           by unfold arm; simp only [h_pc, EXEC_0 s₀ _ h_loaded]⟩
  · intro s₁ h_arm1
    -- h_arm1 : arm s₀ s₁  ⟹  s₁ = step ADD s₀
    have h_eq1 : s₁ = step (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) s₀ := by
      unfold arm at h_arm1; simp only [h_pc, EXEC_0 s₀ _ h_loaded] at h_arm1; exact h_arm1
    -- Derived facts about s₁
    have h_s1_pc : s₁.read_reg Reg.PC = BitVec.ofNat 64 pc + 4 := by
      rw [h_eq1]; unfold step; simp [ArmState.read_write_same, h_pc]
    have h_s1_x1 : s₁.read_reg Reg.X1 = BitVec.ofNat 64 b := by
      rw [h_eq1]; unfold step
      simp [ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X1),
            ArmState.read_write_diff _ _ _ _ (by decide : Reg.X2 ≠ Reg.X1), h_x1]
    have h_s1_x2 : s₁.read_reg Reg.X2 = BitVec.ofNat 64 b + BitVec.ofNat 64 a := by
      rw [h_eq1]; unfold step
      simp [ArmState.read_write_same,
            ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X2),
            h_x1, h_x0]
    have h_s1_loaded : aligned_bytes_loaded s₁.mem (BitVec.ofNat 64 pc) simple_mc := by
      rw [h_eq1]; unfold step; simp [ArmState.write_reg, h_loaded]
    -- Step s1 → s2: execute SUB X2, X2, X1
    apply eventually.ind
    · exact ⟨step (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) s₁,
             by unfold arm; simp only [h_s1_pc, EXEC_4 s₁ _ h_s1_loaded]⟩
    · intro s₂ h_arm2
      -- h_arm2 : arm s₁ s₂  ⟹  s₂ = step SUB s₁
      have h_eq2 : s₂ = step (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) s₁ := by
        unfold arm at h_arm2; simp only [h_s1_pc, EXEC_4 s₁ _ h_s1_loaded] at h_arm2
        exact h_arm2
      apply eventually.base
      constructor
      · constructor
        · -- PC = pc + 8
          rw [h_eq2]; unfold step
          simp only [ArmState.read_write_same, BitVec.ofNat_eq_ofNat]
          bv_omega
        · -- X2 = a
          rw [h_eq2]; unfold step
          simp [ArmState.read_write_same,
                ArmState.read_write_diff _ _ _ _ (by decide : Reg.PC ≠ Reg.X2),
                h_s1_x2, h_s1_x1, BitVec.add_comm, BitVec.add_sub_cancel]
      · -- Frame: only PC and X2 changed
        unfold maychange_regs unchanged_reg
        intro r h_not_in
        simp only [List.mem_cons] at h_not_in
        push Not at h_not_in
        obtain ⟨h_ne_pc, h_ne_x2, _⟩ := h_not_in
        rw [h_eq2, h_eq1]; unfold step
        simp [ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_x2),
              ArmState.read_write_diff _ _ _ _ (Ne.symm h_ne_pc)]

end Bignum.Arm.Tutorial
