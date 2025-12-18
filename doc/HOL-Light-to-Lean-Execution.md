# HOL Light to Lean 4: Program Execution Mapping

This document explains how ARM program execution is modeled in HOL Light (s2n-bignum) and how it was translated to Lean 4 (Bignum-Lean).

## Overview

Both systems use **operational semantics** to model ARM instruction execution, but they differ significantly in their implementation approach:

- **HOL Light**: Uses a **component-based** state model with theorem-based decoding and tactical symbolic execution
- **Lean 4**: Uses **direct struct access** with functional execution model

## 1. State Representation

### HOL Light (s2n-bignum)

HOL Light uses a **component abstraction** system (defined in `common/components.ml`):

```ocaml
(* Components provide read/write access with `:>` composition *)
read PC s          (* Read PC register from state s *)
write PC val s     (* Write val to PC in state s *)
X0 :> zerotop_32   (* W0 is X0 with top 32 bits zeroed *)
```

**Key features:**
- Components are abstract lenses: `(S,V)component`
- Composition operator: `c1 :> c2` composes components
- State updates are relational: `(reg := val) s s'` relates states

**Example:**
```ocaml
(PC := word_add (read PC s) (word 4) ,,
 X2 := word_add (read X1 s) (read X0 s)) s s'
```

### Lean 4 (Bignum-Lean)

Lean uses **direct structure access** with built-in record syntax:

```lean
-- Direct field access
s.read_reg Reg.PC       -- Read PC register
s.write_reg Reg.PC val  -- Write val to PC (returns new state)

-- Chained updates using pipe operator
s.write_reg Reg.X2 result
 |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)
```

**Key features:**
- Functions return new states (pure functional)
- No composition operator needed - use `.` or `|>`
- Updates are functional: `write_reg : Reg → Word64 → ArmState → ArmState`

**Source mapping:**
- Lean: `Bignum/Arm/Machine/State.lean:42-59` (read_reg, write_reg)
- HOL Light: `common/components.ml` (NOT ported - unnecessary in Lean)

## 2. Instruction Semantics

### HOL Light Approach

HOL Light uses **theorem-based decoding** with relational semantics:

```ocaml
(* Step 1: Decode bytecode into instruction theorem *)
let EXEC = ARM_MK_EXEC_RULE simple_mc;;
(* EXEC is a theorem array mapping PC offset → instruction *)

(* Step 2: Each instruction has relational semantics *)
arm_decode s (word pc) instr  (* Instruction at PC is 'instr' *)
arm_execute instr s s'        (* Executing 'instr' relates s to s' *)

(* Step 3: The 'arm' predicate combines decode + execute *)
arm s s' <=>
  ?instr. arm_decode s (read PC s) instr /\
          (PC := word_add (read PC s) (word 4) ,,
           arm_execute instr) s s'
```

**Key characteristics:**
- **Relational**: `instr : armstate → armstate → bool`
- Theorem-driven: Instructions are proved to satisfy semantics
- State transitions are relations, not functions

**Source:** `s2n-bignum/arm/proofs/arm.ml:188-196`

### Lean 4 Approach

Lean uses **functional execution** with direct evaluation:

```lean
-- Step 1: Program is data structure with instruction list
def simple_program : Program := {
  base_addr := Word64.ofNat 0
  instructions := [
    Instruction.ADD Reg.X2 Reg.X1 Reg.X0,
    Instruction.SUB Reg.X2 Reg.X2 Reg.X1
  ]
}

-- Step 2: Single instruction execution is a function
def step (instr : Instruction) (s : ArmState) : ArmState :=
  match instr with
  | Instruction.ADD rd rn rm =>
    let result := s.read_reg rn + s.read_reg rm
    s.write_reg rd result
     |>.write_reg Reg.PC (s.read_reg Reg.PC + 4)
  | ...

-- Step 3: Program execution is sequential composition
def exec (instrs : List Instruction) (s : ArmState) : ArmState :=
  instrs.foldl (fun state instr => step instr state) s

def exec_program (prog : Program) (s : ArmState) : ArmState :=
  if s.read_reg Reg.PC = prog.base_addr then
    exec prog.instructions s
  else
    s
```

**Key characteristics:**
- **Functional**: `step : Instruction → ArmState → ArmState`
- Direct evaluation: No theorem proving during execution
- Deterministic: Function returns the final state

**Source:** `Bignum/Arm/Machine/Semantics.lean:42-186`

## 3. Symbolic Execution: How Programs Are "Run"

### HOL Light: Tactical Symbolic Execution

HOL Light uses **proof tactics** to symbolically execute instructions:

```ocaml
let SIMPLE_SPEC = prove(
  `forall pc a b. ensures arm
    (\s. read PC s = word pc /\ read X0 s = word a /\ read X1 s = word b)
    (\s. read PC s = word (pc+8) /\ read X2 s = word a)
    (MAYCHANGE [PC;X2])`,

  (* Proof tactics: *)
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN           (* Initialize symbolic state s0 *)
  ARM_STEPS_TAC EXEC (1--2) THEN       (* Execute instructions 1-2 *)
  ENSURES_FINAL_STATE_TAC THEN         (* Prove postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;                (* Solve word arithmetic *)
```

**What `ARM_STEPS_TAC EXEC (1--2)` does:**

1. **Lookup instruction**: Uses `EXEC` theorem array: `EXEC[0]` gives first instruction theorem
2. **Apply semantics**: Instantiates the relational semantics for that instruction
3. **Generate intermediate state**: Creates `s1`, `s2`, ... for each step
4. **Build execution trace**: Proves `arm s0 s1`, `arm s1 s2`, etc.
5. **Symbolic evaluation**: Rewrites state expressions:
   - After ADD: `read X2 s1 = word_add (word b) (word a)`
   - After SUB: `read X2 s2 = word_sub (word_add (word b) (word a)) (word b)`

**The result is a theorem** (not a value):
```
⊢ read PC s0 = word pc ∧ read X0 s0 = word a ∧ read X1 s0 = word b
  ⟹ read PC s2 = word (pc+8) ∧ read X2 s2 = word a
```

**Source:** `s2n-bignum/arm/tutorial/simple.ml:86-101`

### Lean 4: Functional Evaluation with Proof

Lean separates **execution** from **verification**:

```lean
-- Execution: Just run the program (computable)
def exec_program (prog : Program) (s : ArmState) : ArmState :=
  if s.read_reg Reg.PC = prog.base_addr then
    exec prog.instructions s
  else
    s

-- Verification: Prove correctness theorem
theorem simple_correct (pc a b : ℕ)
    (h_sum_bound : a + b < 2 ^ 64) :
    (simple_spec pc a b).satisfies := by
  unfold Ensures.satisfies simple_spec
  intro s_init h_pre
  unfold exec_program simple_program exec step

  -- Manual symbolic reasoning in proof
  let s1 := s_init.write_reg Reg.X2
              (s_init.read_reg Reg.X1 + s_init.read_reg Reg.X0)
           |>.write_reg Reg.PC (s_init.read_reg Reg.PC + 4)

  have h_s1_x2 : s1.read_reg Reg.X2
               = s_init.read_reg Reg.X1 + s_init.read_reg Reg.X0 := by sorry

  -- Arithmetic: (b + a) - b = a
  have h_word_arith : Word64.ofNat b + Word64.ofNat a - Word64.ofNat b
                    = Word64.ofNat a := by sorry

  sorry  -- Complete proof
```

**Key differences:**
- `exec_program` is **computable** - you can actually run it: `#eval exec_program ...`
- Proof is **separate** from execution
- No automatic symbolic execution tactic (yet)
- Requires manual proof of each step

**Source:** `Bignum/Arm/Tutorial/Simple.lean:172-230`

## 4. Specification System: `ensures`

### HOL Light `ensures` (Hoare Triple)

```ocaml
ensures arm
  (\s. precondition)
  (\s. postcondition)
  (MAYCHANGE [PC; X2])
```

**Semantics (theorem to prove):**
```
∀s. precondition s ⟹
    ∃s'. arm* s s' ∧ postcondition s' ∧ maychange_only [PC;X2] s s'
```

Where `arm*` is the reflexive-transitive closure of the `arm` relation (multi-step execution).

**Source:** HOL Light tactics library (standard Hoare logic)

### Lean 4 `Ensures` (Specification Structure)

```lean
structure Ensures where
  pre : ArmState → Prop              -- Precondition
  post : ArmState → Prop             -- Postcondition
  frame : ArmState → ArmState → Prop -- Frame condition
  prog : Program                      -- The program itself

def Ensures.satisfies (spec : Ensures) : Prop :=
  ∀ s_init, spec.pre s_init →
    let s_final := exec_program spec.prog s_init
    spec.post s_final ∧ spec.frame s_init s_final
```

**Key differences from HOL Light:**
1. **Program is explicit**: `prog : Program` (not implicit in bytecode)
2. **Deterministic execution**: Uses `exec_program` function (not relational `arm*`)
3. **Frame is explicit relation**: `frame : ArmState → ArmState → Prop`

**Frame condition example:**
```lean
-- MAYCHANGE [PC; X2] in HOL Light becomes:
def maychange_regs (regs : List Reg) (s_init s_final : ArmState) : Prop :=
  ∀ r, r ∉ regs → s_final.read_reg r = s_init.read_reg r

def simple_frame : ArmState → ArmState → Prop :=
  maychange_regs [Reg.PC, Reg.X2]
```

**Source:** `Bignum/Arm/Spec/Ensures.lean:55-136`

## 5. Complete Example Comparison

### HOL Light: `simple.ml`

```ocaml
(* 1. Define bytecode *)
let simple_mc = new_definition `simple_mc = [
  word 0x22; word 0x00; word 0x00; word 0x8b;  (* ADD X2, X1, X0 *)
  word 0x42; word 0x00; word 0x01; word 0xcb   (* SUB X2, X2, X1 *)
]`;;

(* 2. Create execution theorems *)
let EXEC = ARM_MK_EXEC_RULE simple_mc;;

(* 3. Prove specification *)
let SIMPLE_SPEC = prove(
  `forall pc a b. ensures arm ...`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--2) THEN  (* Symbolically execute 2 instructions *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;           (* Automatic word arithmetic *)
```

**Proof is automatic** after setup - tactics do the work.

**Source:** `s2n-bignum/arm/tutorial/simple.ml`

### Lean 4: `Simple.lean`

```lean
-- 1. Define program structure
def simple_program : Program := {
  base_addr := Word64.ofNat 0
  instructions := [
    Instruction.ADD Reg.X2 Reg.X1 Reg.X0,
    Instruction.SUB Reg.X2 Reg.X2 Reg.X1
  ]
}

-- 2. Define specification
def simple_spec (pc a b : ℕ) : Ensures := {
  pre := fun s =>
    s.read_reg Reg.PC = Word64.ofNat pc ∧
    s.read_reg Reg.X0 = Word64.ofNat a ∧
    s.read_reg Reg.X1 = Word64.ofNat b

  post := fun s =>
    s.read_reg Reg.PC = Word64.ofNat (pc + 8) ∧
    s.read_reg Reg.X2 = Word64.ofNat a

  frame := maychange_regs [Reg.PC, Reg.X2]
  prog := simple_program
}

-- 3. Prove correctness
theorem simple_correct (pc a b : ℕ) ... :
    (simple_spec pc a b).satisfies := by
  unfold Ensures.satisfies simple_spec exec_program exec step
  -- Manual proof steps with sorry placeholders
  ...
```

**Proof is manual** - requires explicit reasoning about each step.

**Source:** `Bignum/Arm/Tutorial/Simple.lean`

## 6. Key Translation Challenges

### Challenge 1: No Symbolic Execution Tactic

**HOL Light:** `ARM_STEPS_TAC EXEC (1--2)` automatically:
- Looks up instructions from EXEC array
- Applies semantics
- Simplifies symbolic expressions
- Generates intermediate states

**Lean 4:** Currently manual - need to:
- Explicitly unfold definitions
- Manually construct intermediate states
- Prove lemmas about read/write interaction
- Use `sorry` for BitVec arithmetic

**Solution needed:** Build tactics for symbolic execution (future work).

### Challenge 2: Word Arithmetic Automation

**HOL Light:** `CONV_TAC WORD_RULE` solves:
```
word_sub (word_add (word b) (word a)) (word b) = word a
```

**Lean 4:** Requires manual proof with BitVec lemmas:
```lean
have h_word_arith : Word64.ofNat b + Word64.ofNat a - Word64.ofNat b
                  = Word64.ofNat a := by sorry
```

**Solution needed:** Import/develop BitVec arithmetic library (Mathlib).

### Challenge 3: Component Abstraction

**HOL Light:** Uses abstract components with composition:
```ocaml
(PC := val1 ,, X2 := val2) s s'   (* Compose updates *)
X0 :> zerotop_32                   (* Compose lenses *)
```

**Lean 4:** Uses direct struct operations - simpler but less abstract:
```lean
s.write_reg Reg.PC val1 |>.write_reg Reg.X2 val2
-- No composition operator, just function chaining
```

**Design decision:** Lean's approach is more idiomatic and easier to understand.

## 7. Summary Table

| Aspect                 | HOL Light                    | Lean 4                  |
|------------------------|------------------------------|-------------------------|
| **State Model**        | Component-based lenses       | Direct struct access    |
| **Execution**          | Relational (`s → s' → bool`) | Functional (`s → s'`)   |
| **Decoding**           | Theorem array from bytecode  | Data structure (direct) |
| **Symbolic Execution** | Automatic (`ARM_STEPS_TAC`)  | Manual (unfold + proof) |
| **Word Arithmetic**    | Automatic (`WORD_RULE`)      | Manual (BitVec lemmas)  |
| **Frame Condition**    | `MAYCHANGE [regs]`           | `maychange_regs [regs]` |
| **Proof Style**        | Tactical (automatic)         | Term + tactic (manual)  |
| **Executability**      | Symbolic only                | Computable + provable   |

## 8. File References

### Lean 4 (this project)
- **State**: `Bignum/Arm/Machine/State.lean`
- **Semantics**: `Bignum/Arm/Machine/Semantics.lean`
- **Ensures**: `Bignum/Arm/Spec/Ensures.lean`
- **Example**: `Bignum/Arm/Tutorial/Simple.lean`

### HOL Light (s2n-bignum)
- **State & Components**: `common/components.ml` (NOT ported)
- **ARM Model**: `arm/proofs/arm.ml`
- **Base Infrastructure**: `arm/proofs/base.ml`
- **Example**: `arm/tutorial/simple.ml`

## 9. Future Work

To match HOL Light's proof automation, Bignum-Lean needs:

1. **Symbolic execution tactic**: Automate the `step` unfolding and intermediate state construction
2. **BitVec arithmetic library**: Lemmas for `(a + b) - b = a` with modular arithmetic
3. **Read/write interaction lemmas**:
   - `(s.write_reg r v).read_reg r = v`
   - `(s.write_reg r1 v).read_reg r2 = s.read_reg r2` (when `r1 ≠ r2`)
4. **Frame automation**: Tactic to automatically verify frame conditions

These are planned for **Phase 1** (Machine Model completion).

---

**Document Status:** Complete
**Last Updated:** 2025-12-05
**Author:** Claude Code (based on codebase analysis)
