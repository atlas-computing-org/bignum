# Bignum-Lean: Port of s2n-bignum to Lean 4

A port of Amazon's [s2n-bignum](https://github.com/awslabs/s2n-bignum)
formal verification from HOL Light to Lean 4.

## Overview

This project aims to port the formally verified cryptographic
arithmetic library s2n-bignum from HOL Light to Lean 4. The s2n-bignum
library provides high-performance, constant-time implementations of
big integer arithmetic operations used in cryptography, with
machine-checked proofs of correctness.

## Project Structure

```
bignum-lean/
├── Bignum/
│   ├── Common/                  # Shared between architectures
│   │   ├── Basic/
│   │   │   ├── Defs.lean        # bigdigit, highdigits, lowdigits
│   │   │   └── Lemmas.lean      # Core theorems
│   │   ├── Word.lean            # 64-bit word arithmetic
│   │   └── Memory.lean          # Memory model
│   │
│   ├── Arm/                     # ARM-specific (AArch64)
│   │   ├── Machine/
│   │   │   ├── State.lean       # ARM state (registers, flags, memory)
│   │   │   ├── Instruction.lean # ARM instruction types
│   │   │   ├── Decode.lean      # Instruction decoder (bytes → instructions)
│   │   │   └── Semantics.lean   # Operational semantics
│   │   ├── Spec/
│   │   │   └── Ensures.lean     # Pre/post/frame specifications
│   │   ├── Generic/             # Generic bignum operations (future)
│   │   ├── Curve/               # Elliptic curve operations (future)
│   │   └── Tutorial/            # Port of arm tutorials
│   │
│   └── X86/                     # x86-64-specific (future)
│       ├── Machine/
│       ├── Spec/
│       ├── Generic/
│       ├── Curve/
│       └── Tutorial/
│
└── s2n-bignum/                  # Original HOL Light source (submodule)
```

## Correspondence with s2n-bignum

Each Lean file documents its correspondence with the original HOL
Light source. The structure mirrors s2n-bignum's organization by
architecture:

### Core Infrastructure

| Lean File                             | HOL Light Source                          | Description             |
|---------------------------------------|-------------------------------------------|-------------------------|
| `Bignum/Common/Basic/Defs.lean`       | `s2n-bignum/common/bignum.ml:11-77`       | Core bignum definitions |
| `Bignum/Common/Basic/Lemmas.lean`     | `s2n-bignum/common/bignum.ml:79-150`      | Fundamental theorems    |
| `Bignum/Common/Word.lean`             | HOL Light `Library/words.ml`              | 64-bit word operations  |
| `Bignum/Common/Memory.lean`           | `s2n-bignum/common/components.ml`         | Memory model            |
| `Bignum/Arm/Machine/State.lean`       | `s2n-bignum/arm/proofs/arm.ml`            | ARM machine state       |
| `Bignum/Arm/Machine/Instruction.lean` | `s2n-bignum/arm/proofs/instruction.ml`    | ARM instructions        |
| `Bignum/Arm/Machine/Decode.lean`      | `s2n-bignum/arm/proofs/decode.ml`         | Instruction decoder     |
| `Bignum/Arm/Machine/Semantics.lean`   | `s2n-bignum/arm/proofs/arm.ml`            | Instruction semantics   |
| `Bignum/Arm/Spec/Ensures.lean`        | `s2n-bignum/arm/tutorial/simple.ml:65-84` | Specification framework |


## Building

```bash
lake build
```

## Development Plan

The development plan follows the s2n-bignum tutorial progression. Each
phase implements one tutorial, incrementally building the verification
infrastructure. After completing all ARM tutorials, we'll expand to
x86-64.

### ✅ Phase 0: Foundations (Complete)

**Goal:** Verify a simple 2-instruction linear program

**What we built:**
- Core bignum definitions (bigdigit, highdigits, lowdigits)
- ARM state model (registers, flags, memory)
- Basic instructions (ADD, SUB, ADCS)
- Operational semantics (instruction execution)
- Specification framework (`ensures` with pre/post/frame)
- Instruction decoder (bytes → instructions)

**Deliverable:** `Bignum/Arm/Tutorial/Simple.lean`

### 🚧 Phase 1: Program Composition

**Goal:** Verify programs by splitting into sequential chunks with
intermediate assertions

**New capabilities needed:**
- Instructions: `MOV`, `MUL`
- Tactic: `ENSURES_SEQUENCE_TAC` (split program with intermediate state)
- .o file parser: `define_assert_from_elf` (extract bytecode from ELF)

**Deliverable:** `Bignum/Arm/Tutorial/Sequence.lean`


### Phase 2: Conditional Branching

**Goal:** Verify programs with conditional branches

**New capabilities needed:**
- Instructions: `CMP` (comparison with flags), `B.HI` (conditional
  branch), `RET`
- Flag reasoning: `SOME_FLAGS`, condition codes (ZF, CF, NF, VF)
- Case analysis: branch taken vs not taken
- Events: microarchitectural event tracking

**Deliverable:** `Bignum/Arm/Tutorial/Branch.lean`


### Phase 3: Memory Operations

**Goal:** Verify programs that read/write memory

**New capabilities needed:**
- Instructions: `LDR` (load register), `STR` (store register)
- Memory model: `bytes64`, reading/writing 64-bit words
- Preconditions: `nonoverlapping` (aliasing constraints)
- MAYCHANGE: track memory locations that may change

**Deliverable:** `Bignum/Arm/Tutorial/Memory.lean`


### Phase 4: Loops

**Goal:** Verify programs with simple loops using invariants

**New capabilities needed:**
- Instructions: `B.NE` (branch if not equal)
- Tactic: `ENSURES_WHILE_PAUP_TAC` (loop invariant tactic)
- Loop invariants: relate loop counter to program state
- Backedge reasoning: prove loop continues until condition

**Deliverable:** `Bignum/Arm/Tutorial/Loop.lean`


### Phase 5: Bignum Operations

**Goal:** Verify programs operating on multi-word bignums

**New capabilities needed:**
- Instructions: `LDP` (load pair of registers)
- Abstraction: `bignum_from_memory` (read multi-word values)
- Tactic: `BIGNUM_DIGITIZE_TAC` (split bignum into digits)
- Full .o parser: complete `define_assert_from_elf` implementation

**Deliverable:** `Bignum/Arm/Tutorial/Bignum.lean`


### Phase 6: Read-Only Data

**Goal:** Verify programs that read from .rodata section

**New capabilities needed:**
- Instructions: `ADRP` (page-relative address), `ADD` (with
  immediate), `B` (unconditional branch)
- PC-relative addressing: compute addresses relative to program counter
- Relocation parser: `define_assert_relocs_from_elf`
- Read-only section: `bytelist` for constant data
- Subroutines: `ARM_SUBROUTINE_SIM_TAC` (function call reasoning)

**Deliverable:** `Bignum/Arm/Tutorial/Rodata.lean`


### Phase 7: Relational Reasoning - Basics

**Goal:** Prove equivalence of two simple straight-line programs

**New capabilities needed:**
- Framework: `ensures2` (relational Hoare triple)
- Tactics:
  - `ENSURES2_INIT_TAC` (initialize relational symbolic execution)
  - `ARM_N_STUTTER_LEFT_TAC` (execute left program only)
  - `ARM_N_STUTTER_RIGHT_TAC` (execute right program only)
  - `META_EXISTS_TAC`, `UNIFY_REFL_TAC` (unification)
  - `MONOTONE_MAYCHANGE_CONJ_TAC`

**Deliverable:** `Bignum/Arm/Tutorial/RelSimp.lean`


### Phase 8: Relational Reasoning - Equivalence Tactics

**Goal:** Prove equivalence using actions (diff-based approach)

**New capabilities needed:**
- Helper: `mk_equiv_statement_simple` (build equivalence goal)
- Predicates: `eqin`, `eqout` (input/output state equivalence)
- Tactics:
  - `EQUIV_INITIATE_TAC`
  - `EQUIV_STEPS_TAC` (lockstep + stuttering based on actions)
- Actions: list of ("equal", ...) and ("replace", ...) for instruction alignment

**Deliverable:** `Bignum/Arm/Tutorial/RelEquivTac.lean`


### Phase 9: Relational Reasoning - Reordering

**Goal:** Prove equivalence of programs with reordered instructions

**New capabilities needed:**
- Tactics:
  - `ARM_N_STEPS_AND_ABBREV_TAC` (execute with abbreviations)
  - `ARM_N_STEPS_AND_REWRITE_TAC` (execute and match abbreviations)
- Instruction mapping: list mapping instruction indices between programs

**Deliverable:** `Bignum/Arm/Tutorial/RelReorderTac.lean`


### Phase 10: Relational Reasoning - Loops

**Goal:** Prove equivalence of two loops

**New capabilities needed:**
- Tactic: `ENSURES2_WHILE_PAUP_TAC` (relational loop invariant)
- Loop synchronization: relate loop counters and invariants

**Deliverable:** `Bignum/Arm/Tutorial/RelLoop.lean`


### Phase 11: Relational Reasoning - SIMD/Vectorization

**Goal:** Prove equivalence of scalar vs vectorized implementations
(128×128→256-bit squaring)

**New capabilities needed:**
- SIMD/NEON instructions: `LDR Q`, `UMULL_VEC`, `UMULL2_VEC`, `XTN`, `UZP2`, `UMOV`, `EXTR`
- NEON helper: vector reasoning lemmas and tactics
- Advanced simplification: `WORD_BITMANIP_SIMP_LEMMAS`, custom word equations
- Realistic optimization patterns

**Deliverable:** `Bignum/Arm/Tutorial/RelVecEq.lean`

--- 

After completing all ARM tutorials, expand to x86-64 architecture
following the same tutorial structure (`x86/tutorial/`).


## Design Principles

1. **Incremental Development:** Each phase builds on previous work
2. **Fidelity to Original:** Maintain close correspondence with s2n-bignum
3. **Documentation:** Every definition references its HOL Light source
4. **Reusable Automation:** Build tactic libraries for common patterns
5. **Validation:** Cross-check against s2n-bignum test suite where possible

## Key Differences from HOL Light

| Aspect           | HOL Light                   | Lean 4                                  |
|------------------|-----------------------------|-----------------------------------------|
| **Type System**  | Simple types                | Dependent types                         |
| **Memory Model** | Component abstraction       | Functional map `Address → Option UInt8` |
| **Words**        | `:(N)word` type             | `BitVec 64`                             |
| **Proof Style**  | Tactical (forward/backward) | Tactic + term mode                      |
| **Automation**   | `WORD_RULE` for arithmetic  | Lean tactics and custom tactics         |


## Contributing

When adding new verified functions:

1. Reference the corresponding HOL Light file and line numbers
2. Document the specification (pre/post/frame)
3. Maintain correspondence comments
4. Add to the appropriate module (`Generic/`, `Curve/`, etc.)
5. Update this README with progress

## References

- [s2n-bignum GitHub](https://github.com/awslabs/s2n-bignum)
- [HOL Light](https://github.com/jrh13/hol-light)
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)

