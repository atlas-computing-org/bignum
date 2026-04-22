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

/-- The two decoded instructions (used in proofs and simulation). -/
def simple_instrs : List Instruction :=
  [Instruction.ADD Reg.X2 Reg.X1 Reg.X0,
   Instruction.SUB Reg.X2 Reg.X2 Reg.X1]

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
## Simulation with `#eval`

The computational nature of Lean lets us run the program before proving it.
Both simulation approaches (A and B) are available.
-/

-- Approach A: simulate via pre-decoded exec
-- #eval simulateExec simple_mc 0 [(Reg.X0, 5), (Reg.X1, 3)]

-- Approach B: simulate via fetch-decode-execute loop
-- #eval simulateLoop 2 simple_mc 0 [(Reg.X0, 5), (Reg.X1, 3)]

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

HOL Light proof (5 tactics):
```ocaml
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE
```
-/

/-- Prove that `simple_instrs` decode correctly from a state with `simple_mc` loaded. -/
private theorem simple_decode_list (s : ArmState) (pc : Word64)
    (hb : bytes_loaded s.mem pc simple_mc)
    (h_pc : s.read_reg Reg.PC = pc) :
    arm_decode_list simple_instrs s := by
  constructor
  · have key := exec_at s pc simple_mc 0 hb (by decide)
                  (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) (by decide)
    rwa [show pc + BitVec.ofNat 64 0 = pc from by bv_omega, ← h_pc] at key
  constructor
  · let s₁ := step (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) s
    have h_mem1 : s₁.mem = s.mem := by simp [step, advance_pc, ArmState.write_reg, s₁]
    have h_pc1 : s₁.read_reg Reg.PC = pc + 4 := by
      simp only [ArmState.read_reg, step, advance_pc, ArmState.write_reg, BitVec.ofNat_eq_ofNat,
        ↓reduceIte, BitVec.add_left_inj, s₁]
      rw [← ArmState.read_reg, h_pc]
    have hb' : bytes_loaded s₁.mem pc simple_mc := h_mem1 ▸ hb
    have key := exec_at s₁ pc simple_mc 4 hb' (by decide)
                  (Instruction.SUB Reg.X2 Reg.X2 Reg.X1) (by decide)
    rwa [show pc + BitVec.ofNat 64 4 = pc + 4 from by bv_omega, ← h_pc1] at key
  · trivial

theorem SIMPLE_SPEC (pc a b : ℕ) :
    ensures arm
      (fun s => aligned_bytes_loaded s.mem (BitVec.ofNat 64 pc) simple_mc ∧
                s.read_reg Reg.PC = BitVec.ofNat 64 pc ∧
                s.read_reg Reg.X0 = BitVec.ofNat 64 a ∧
                s.read_reg Reg.X1 = BitVec.ofNat 64 b)
      (fun s => s.read_reg Reg.PC = BitVec.ofNat 64 (pc + 8) ∧
                s.read_reg Reg.X2 = BitVec.ofNat 64 a)
      (maychange_regs [Reg.PC, Reg.X2]) := by
  apply ensures_of_exec simple_instrs
  · -- Decode: instructions decode correctly from memory
    intro s ⟨h_loaded, h_pc, _, _⟩
    exact simple_decode_list s _ h_loaded.2 h_pc
  · -- Post: postcondition holds on exec simple_instrs s
    intro s ⟨_, h_pc, h_x0, h_x1⟩
    simp only [exec, simple_instrs, List.foldl,
               step, advance_pc, ArmState.write_reg, ArmState.read_reg]
    rw [show s.regs Reg.PC = BitVec.ofNat 64 pc from h_pc]
    rw [show s.regs Reg.X0 = BitVec.ofNat 64 a  from h_x0]
    rw [show s.regs Reg.X1 = BitVec.ofNat 64 b  from h_x1]
    simp only [Reg.X2, Reg.X1, if_true]
    constructor
    · bv_omega
    · simp only [Fin.isValue, reduceCtorEq, ↓reduceIte, Reg.X.injEq, Fin.reduceEq]
      bv_omega
  · -- Frame: only PC and X2 changed
    intro s _ r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    obtain ⟨hne_pc, hne_x2⟩ := hr
    simp only [unchanged_reg, exec, simple_instrs, List.foldl,
               step, advance_pc, ArmState.write_reg, ArmState.read_reg]
    simp [hne_pc, hne_x2]

end Bignum.Arm.Tutorial
