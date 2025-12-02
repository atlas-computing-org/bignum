# Bignum-Lean: Formal Verification of s2n-bignum in Lean 4

A port of Amazon's [s2n-bignum](https://github.com/awslabs/s2n-bignum) formal verification from HOL Light to Lean 4.

## Overview

This project aims to port the formally verified cryptographic arithmetic library s2n-bignum from HOL Light to Lean 4. The s2n-bignum library provides high-performance, constant-time implementations of big integer arithmetic operations used in cryptography, with machine-checked proofs of correctness.

## Project Structure

```
bignum-lean/
├── Bignum/
│   ├── Common/                  # Shared between architectures
│   │   ├── Basic/
│   │   │   ├── Defs.lean       # bigdigit, highdigits, lowdigits
│   │   │   └── Lemmas.lean     # Core theorems
│   │   ├── Word.lean           # 64-bit word arithmetic
│   │   └── Memory.lean         # Memory model
│   │
│   ├── Arm/                     # ARM-specific (AArch64)
│   │   ├── Machine/
│   │   │   ├── State.lean      # ARM state (registers, flags, memory)
│   │   │   ├── Instruction.lean # ARM instruction types
│   │   │   └── Semantics.lean  # Operational semantics
│   │   ├── Spec/
│   │   │   └── Ensures.lean    # Pre/post/frame specifications
│   │   ├── Generic/            # Generic bignum operations (future)
│   │   ├── Curve/              # Elliptic curve operations (future)
│   │   └── Tutorial/
│   │       └── Simple.lean     # Port of arm/tutorial/simple.ml
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

## Current Status

### ✅ Phase 0: Foundations (COMPLETED)

- [x] Basic bignum definitions (`bigdigit`, `highdigits`, `lowdigits`)
- [x] Fundamental theorems (decomposition, bounds, sums)
- [x] 64-bit word arithmetic with carry/borrow
- [x] Memory model (read/write, bignums, alignment)
- [x] ARM state model (registers, flags, memory)
- [x] ARM instruction types (ADD, SUB, ADCS, etc.)
- [x] Operational semantics (instruction execution)
- [x] Specification system (`ensures` with pre/post/frame)
- [x] Tutorial example (port of `s2n-bignum/arm/tutorial/simple.ml`)

### 🚧 Next Steps

See [Development Plan](#development-plan) below.

## Correspondence with s2n-bignum

Each Lean file documents its correspondence with the original HOL Light source:

| Lean File | HOL Light Source | Description |
|-----------|------------------|-------------|
| `Bignum/Common/Basic/Defs.lean` | `s2n-bignum/common/bignum.ml:11-77` | Core bignum definitions |
| `Bignum/Common/Basic/Lemmas.lean` | `s2n-bignum/common/bignum.ml:79-150` | Fundamental theorems |
| `Bignum/Common/Word.lean` | HOL Light `Library/words.ml` | 64-bit word operations |
| `Bignum/Common/Memory.lean` | `s2n-bignum/common/components.ml` | Memory model |
| `Bignum/Arm/Machine/State.lean` | `s2n-bignum/arm/proofs/arm.ml` | ARM machine state |
| `Bignum/Arm/Machine/Instruction.lean` | `s2n-bignum/arm/proofs/instruction.ml` | ARM instructions |
| `Bignum/Arm/Machine/Semantics.lean` | `s2n-bignum/arm/proofs/arm.ml` | Instruction semantics |
| `Bignum/Arm/Spec/Ensures.lean` | `s2n-bignum/arm/tutorial/simple.ml:65-84` | Specification framework |
| `Bignum/Arm/Tutorial/Simple.lean` | `s2n-bignum/arm/tutorial/simple.ml` | Complete tutorial port |

## Architecture Organization

The structure mirrors s2n-bignum's organization by architecture:

```
s2n-bignum/          →  Bignum/
├── common/          →  ├── Common/      (shared definitions)
├── arm/             →  ├── Arm/         (ARM AArch64)
│   ├── tutorial/    →  │   └── Tutorial/
│   ├── generic/     →  │   └── Generic/
│   └── proofs/      →  │   └── Machine/ + Spec/
└── x86/             →  └── X86/         (x86-64, future)
```

This organization allows:
- ✅ Clear separation between architectures
- ✅ Shared code in `Common/` (used by both ARM and x86)
- ✅ Easy addition of x86 without restructuring
- ✅ Direct correspondence with s2n-bignum file locations

## Building

```bash
lake build
```

## Development Plan

### Phase 1: ARM Machine Model (3-4 weeks)

**Goal:** Complete executable ARM model with full instruction set

**Tasks:**
1. Expand instruction coverage (memory ops, branches, conditional execution)
2. Implement symbolic execution tactics
3. Develop automation for common proof patterns
4. Validate against s2n-bignum test cases

**Deliverable:** Fully functional ARM simulator in Lean

---

### Phase 2: First Real Function - `bignum_add` (3-4 weeks)

**Goal:** Complete formal verification of `bignum_add`

**Why `bignum_add`?**
- Fundamental operation (used by all others)
- Relatively simple (only additions with carry)
- Tests all components: loops, branches, memory, carry propagation
- HOL Light proof is ~800 lines (manageable size)

**Tasks:**
1. Write formal specification matching `s2n-bignum/arm/proofs/bignum_add.ml:82-100`
2. Translate assembly code to instruction list
3. Prove correctness using symbolic execution
4. Extract reusable proof patterns

**Deliverable:** `Bignum/Arm/Generic/Add.lean` with complete proof

---

### Phase 3: Basic Arithmetic Operations (4-6 weeks)

**Goal:** Build library of verified basic operations

**Priority Functions:**
1. `bignum_sub` (subtraction with borrow)
2. `bignum_eq`, `bignum_lt`, `bignum_le` (comparisons)
3. `bignum_shl_small`, `bignum_shr_small` (shifts)
4. `bignum_mul` (multiplication - more complex)
5. `word_clz`, `word_max`, `word_min` (word operations)

**Deliverable:** ~10-15 verified functions

---

### Phase 4: Modular Arithmetic (4-6 weeks)

**Goal:** Montgomery arithmetic and modular operations

**Functions:**
- `bignum_mod`, `bignum_modadd`, `bignum_modsub`
- `bignum_montmul`, `bignum_montredc`, `bignum_montifier`
- `bignum_modinv` (extended Euclidean algorithm)

**Challenges:**
- Complex algorithmic invariants
- Deep mathematical properties (Montgomery reduction correctness)

**Deliverable:** Complete modular arithmetic library

---

### Phase 5: Elliptic Curves (6-12 weeks, optional)

**Goal:** Full elliptic curve operations

**Scope:**
- Field arithmetic for P-256, P-384, or Curve25519
- Point operations (Jacobian addition, doubling)
- Scalar multiplication

**Note:** This phase is ambitious and may require significant effort.

---

## Design Principles

1. **Incremental Development:** Each phase builds on previous work
2. **Fidelity to Original:** Maintain close correspondence with s2n-bignum
3. **Documentation:** Every definition references its HOL Light source
4. **Reusable Automation:** Build tactic libraries for common patterns
5. **Validation:** Cross-check against s2n-bignum test suite where possible

## Key Differences from HOL Light

| Aspect | HOL Light | Lean 4 |
|--------|-----------|--------|
| **Type System** | Simple types | Dependent types |
| **Memory Model** | Component abstraction | Functional map `Address → Option UInt8` |
| **Words** | `:(N)word` type | `BitVec 64` |
| **Proof Style** | Tactical (forward/backward) | Tactic + term mode |
| **Automation** | `WORD_RULE` for arithmetic | Need custom tactics or `omega`/`polyrith` |

## Contributing

When adding new verified functions:

1. Reference the corresponding HOL Light file and line numbers
2. Document the specification (pre/post/frame)
3. Maintain correspondence comments
4. Add to the appropriate module (`Generic/`, `Curve/`, etc.)
5. Update this README with progress

## References

- [s2n-bignum GitHub](https://github.com/awslabs/s2n-bignum)
- [s2n-bignum Tutorial](https://github.com/awslabs/s2n-bignum/blob/main/arm/tutorial/simple.ml)
- [HOL Light](https://github.com/jrh13/hol-light)
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)

## License

Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0

This project ports work originally licensed under Apache-2.0 OR ISC OR MIT-0 (s2n-bignum).
