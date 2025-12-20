# s2n-bignum Tutorial Analysis

Detailed analysis of each s2n-bignum ARM tutorial, documenting the exact requirements for porting to Lean 4.

## Unary Reasoning Tutorials

### 1. `simple.ml` - ✅ COMPLETE

**What it proves:** `x2 := (x1 + x0) - x1` results in `x2 = x0`

**Instructions:**
- `ADD X2, X1, X0`
- `SUB X2, X2, X1`

**Infrastructure required:**
- ✅ Basic instruction decoder
- ✅ `ensures` predicate (pre/post/frame)
- ✅ `aligned_bytes_loaded` (program loading)
- ✅ Symbolic execution (ARM_STEPS_TAC equivalent)
- ✅ Word arithmetic solver (WORD_RULE equivalent)
- ✅ State model (registers, PC, memory)

**Tactics used:**
- `ENSURES_INIT_TAC "s0"` - initialize symbolic execution
- `ARM_STEPS_TAC EXEC (1--2)` - execute 2 instructions
- `ENSURES_FINAL_STATE_TAC` - finalize and check postcondition
- `CONV_TAC WORD_RULE` - word arithmetic solver

**Lean status:** Implemented in `Bignum/Arm/Tutorial/Simple.lean`

---

### 2. `sequence.ml` - 🚧 IN PROGRESS

**What it proves:** Split program into two chunks with intermediate assertion

**Program:**
```
0: add x1, x1, x0
4: add x2, x2, x0
8: mov x3, #0x2
c: mul x1, x1, x3
```

**Proves:** Final `x1 = (x1_initial + x0) * 2`

**Instructions:**
- `ADD` (already have)
- `MOV X3, #0x2` - move immediate ⭐ NEW
- `MUL X1, X1, X3` - multiply ⭐ NEW

**New infrastructure:**
- `ENSURES_SEQUENCE_TAC pc_mid intermediate_assertion` - split program at PC
  - Creates two subgoals: [pc_start, pc_mid) and [pc_mid, pc_end)
  - Postcondition of first = precondition of second
- `.o file parser` - `define_assert_from_elf` (reads ELF, extracts bytecode)

**Tactics used:**
- `ENSURES_SEQUENCE_TAC`
- `CONJ_TAC THENL [...]` - split into two subgoals

**Key insight:** Compositional reasoning - prove complex programs by breaking into simpler parts

---

### 3. `branch.ml`

**What it proves:** `max(x1, x2)` implementation with conditional branch

**Program:**
```
0:  cmp     x1, x2
4:  b.hi    10 <BB2>
8:  mov     x0, x2
c:  ret

10 <BB2>:
10: mov     x0, x1
14: ret
```

**Proves:** `x0 = word_umax (word a) (word b)`

**Instructions:**
- `CMP X1, X2` - compare, sets flags ⭐ NEW
- `B.HI label` - branch if higher (unsigned) ⭐ NEW
- `MOV X0, X2` (already planned)
- `RET X30` - return ⭐ NEW

**New infrastructure:**
- **Flag handling:**
  - `SOME_FLAGS` - set of condition flags (ZF, CF, NF, VF)
  - Flag computation from compare instructions
  - Conditional execution based on flags
- **Control flow:**
  - Conditional branches (symbolic PC has `if` expression)
  - `COND_CASES_TAC` - case analysis on branch condition
  - Multiple basic blocks
- **Events:**
  - `MAYCHANGE [events]` - microarchitectural events from branches

**Tactics used:**
- `FIRST_X_ASSUM MP_TAC` - move assumption to goal
- `COND_CASES_TAC` - case split on if-then-else
- `POP_ASSUM (LABEL_TAC "name")` - name hypothesis
- `REMOVE_THEN "name" MP_TAC` - retrieve labeled hypothesis
- `ARITH_TAC` - arithmetic reasoning

**Theorems needed:**
- `WORD_UMAX` - definition of unsigned max
- `VAL_WORD_SUB_EQ_0` - `val(x - y) = 0 ↔ val(x) = val(y)`

**Key insight:** Case analysis on symbolic conditions, branch reasoning

---

### 4. `memory.ml`

**What it proves:** Swap two 64-bit words at addresses x0 and x1

**Program:**
```
0: ldr x2, [x0]
4: ldr x3, [x1]
8: str x2, [x1]
c: str x3, [x0]
```

**Proves:** Memory at x0 and x1 are swapped (if they don't alias)

**Instructions:**
- `LDR X2, [X0]` - load from memory ⭐ NEW
- `STR X2, [X1]` - store to memory ⭐ NEW

**New infrastructure:**
- **Memory model extensions:**
  - `memory :> bytes64 (word loc)` - read/write 64-bit word at location
  - `nonoverlapping (word loc0, 8) (word loc1, 8)` - aliasing constraints
- **MAYCHANGE extensions:**
  - `MAYCHANGE [memory :> bytes64 (word loc)]` - track memory modifications
  - `MAYCHANGE [events]` - memory access events

**Preconditions:**
- `nonoverlapping (word loc0, 8) (word loc1, 8)` - x0 and x1 don't overlap
- `nonoverlapping (word loc0, 8) (word pc, LENGTH mc)` - data doesn't overlap code
- `nonoverlapping (word loc1, 8) (word pc, LENGTH mc)` - data doesn't overlap code

**Key insight:** Memory operations need aliasing constraints; symbolic execution tracks memory updates

**Note:** Setting `components_print_log := true` shows when memory assumptions are erased

---

### 5. `loop.ml`

**What it proves:** Loop that increments x0 by 2, ten times

**Program:**
```
0: mov x1, xzr
4: mov x0, xzr

loop:
8:  add x1, x1, #0x1
c:  add x0, x0, #0x2
10: cmp x1, #0xa
14: b.ne loop
18: ret
```

**Proves:** Final `x0 = 20`

**Instructions:**
- `MOV X1, XZR` - move from zero register ⭐ NEW
- `CMP X1, #imm` - compare with immediate ⭐ NEW
- `B.NE label` - branch if not equal ⭐ NEW
- Others already covered

**New infrastructure:**
- **Loop invariant reasoning:**
  - `ENSURES_WHILE_PAUP_TAC` - loop tactic (counter goes UP from A)
    - `P` = ends with flag-setting instruction
    - `A` = counter start value
    - `UP` = counter increments
  - Alternative: `ENSURES_WHILE_PUP_TAC` (when start = 0)
- **Loop structure:**
  - Counter begin/end values
  - Loop body start PC
  - Backedge branch PC
  - Loop invariant relating counter to state
  - Backedge condition (e.g., `read ZF s ↔ i = 10`)

**Loop proof obligations:**
1. Counter begin < counter end
2. Entrance to loop (initialize invariant)
3. Loop body (preserve/advance invariant)
4. Backedge condition (when to continue)
5. Loop exit (postcondition from final invariant)

**Tactics used:**
- `ARM_SIM_TAC` - combined tactic: INIT + STEPS + FINAL + postprocessing

**Key insight:** Inductive reasoning with invariants, relating abstract counter to concrete state

---

### 6. `bignum.ml`

**What it proves:** Equality check for 128-bit integers (two 64-bit words)

**Program:**
```
0:  ldp x2, x3, [x0]      // Load pair from buffer x0
4:  ldp x4, x5, [x1]      // Load pair from buffer x1
8:  cmp x2, x4
c:  b.ne bb_false
10: cmp x3, x5
14: b.ne bb_false
18: mov x0, #0x1
1c: ret

bb_false:
20: mov x0, xzr
24: ret
```

**Proves:** Returns 1 if two 128-bit values are equal, 0 otherwise

**Instructions:**
- `LDP X2, X3, [X0]` - load pair of registers ⭐ NEW
- Others already covered

**New infrastructure:**
- **Bignum abstraction:**
  - `bignum_from_memory (word loc, n) s` - read n words as natural number
  - Alternative: `bignum_of_wordlist [w0; w1; ...]` - from word list
  - `BIGNUM_FROM_MEMORY_BYTES` - rewrite to bytes representation
- **Memory digitization:**
  - `BIGNUM_DIGITIZE_TAC "prefix_" term` - split multi-word read into individual words
  - Converts `bytes(loc, 8*n)` → `bytes64(loc)`, `bytes64(loc+8)`, ...
- **ELF parser:**
  - `define_assert_from_elf "name" "file.o" [0x...; 0x...; ...]`
  - Reads .o file, verifies bytecode matches expected instructions
  - Returns machine code definition + execution rule
  - Tools: `print_literal_from_elf`, `save_literal_from_elf`

**Theorems needed:**
- `EQ_DIVMOD` - equality via div and mod: `m DIV p = n DIV p ∧ m MOD p = n MOD p ↔ m = n`
- `MOD_MULT_ADD`, `MOD_LT` - modular arithmetic
- `DIV_MULT_ADD`, `DIV_LT` - division arithmetic

**Key insight:** Multi-word values, symbolic reasoning on natural number representation

---

### 7. `rodata.ml`

**What it proves:** Functions that read constant arrays from .rodata section

**Functions:**
- `f(i)` - reads from two constant arrays x and y, returns `3*(1+i)`
- `g(i)` - calls `f(i + z)` where z is constant from .rodata

**Program (simplified):**
```
f:
0:  mov     x3, x0
4:  adrp    x10, x_data       // Get page address of x_data
8:  add     x10, x10, x_data  // Add offset within page
c:  mov     x1, x3
10: ldr     w1, [x10, x1, lsl #2]  // x_data[i]
14: adrp    x11, y_data
18: add     x11, x11, y_data
1c: mov     x2, x3
20: ldr     w0, [x11, x2, lsl #2]  // y_data[i]
24: add     w0, w1, w0
28: ret

g:
2c: adrp    x10, z_data
30: add     x10, x10, z_data
34: ldr     w1, [x10]         // z_data[0]
38: add     x0, x1, x0        // i + z
3c: b       0 <f>             // Call f
```

**Instructions:**
- `ADRP Xd, label` - form PC-relative address to 4KB page ⭐ NEW
- `ADD Xd, Xn, #imm` - add immediate ⭐ NEW
- `LDR Wd, [Xn, Xm, LSL #k]` - load with shifted register offset ⭐ NEW
- `B label` - unconditional branch ⭐ NEW

**New infrastructure:**
- **PC-relative addressing:**
  - `adrp_within_bounds (word data) (word pc)` - ensures ADRP can reach data
  - `ADRP_ADD_FOLD` - fold ADRP + ADD into single address computation
- **ELF relocations:**
  - `define_assert_relocs_from_elf "name" "file.o" (fun w BL ADR ADRP ADD_rri64 -> [...])`
  - Returns: `(mc_fn, constants_data)` where:
    - `mc_fn : thm` = `⊢ ∀pc x y z. name pc x y z = [bytes...]`
    - `constants_data : thm list` = definitions of .rodata symbols
  - Tools: `print_literal_relocs_from_elf`, `save_literal_relocs_from_elf`
- **Read-only section:**
  - `read (memory :> bytelist (word addr, LENGTH data)) s = data`
  - `BYTELIST_EXPAND_CONV` - expand bytelist equality
  - Local symbols: use `WHOLE_READONLY_data` or custom name via `map_symbol_name`
- **Subroutine calls:**
  - `ARM_SUBROUTINE_SIM_TAC (mc,EXEC,offset,mc,SPEC) args step`
  - Symbolically executes function call using existing spec

**Helper tactics (custom for tutorial):**
- `INTRO_READ_MEMORY_FROM_BYTES8_TAC` - build N-byte read from 1-byte reads
- `EXPLODE_BYTELIST_ASSUM_TAC` - explode bytelist into individual bytes

**Key insight:** Realistic programs need PC-relative data access, function calls, constant arrays

**Note:** Local vs global symbols affect relocation table structure (ELF vs Mach-O differences)

---

## Relational Reasoning Tutorials

### 8. `rel_simp.ml`

**What it proves:** Equivalence of two programs with same functionality

**Program 1:**
```
0: add x0, x0, #1
4: add x1, x1, #2
8: add x0, x0, #3
```

**Program 2:**
```
0: add x0, x0, #4
4: add x1, x1, #2
```

**Proves:** If x0 and x1 start equal in both, they end equal (x0 += 4, x1 += 2)

**New infrastructure:**
- **Relational Hoare triple:**
  - `ensures2 arm` - relate two executions
  - `(\(s1,s2). pre) (\(s1,s2). post) (\(s1,s2) (s1',s2'). frame) (\s. n1) (\s. n2)`
  - Precondition: relation on input states
  - Postcondition: relation on output states
  - Frame: relation on before/after state pairs (left and right)
  - Step counts: `(\s. 3)` and `(\s. 2)` (must be precise!)
- **Relational tactics:**
  - `ENSURES2_INIT_TAC "s0" "s0'"` - initialize both programs
  - `ARM_N_STUTTER_LEFT_TAC EXEC (1--3) None` - execute left only
  - `ARM_N_STUTTER_RIGHT_TAC EXEC (1--2) "'" None` - execute right only (suffix "'" for state names)
  - `REPEAT_N 2 ENSURES_FINAL_STATE_TAC` - finalize both
  - `META_EXISTS_TAC` - eexists for meta-level unification
  - `UNIFY_REFL_TAC` - reflexivity after unification
  - `MONOTONE_MAYCHANGE_CONJ_TAC` - discharge MAYCHANGE conjunction

**Key insight:** Lock-step isn't required; can advance one program while other stays put (stuttering)

---

### 9. `rel_equivtac.ml`

**What it proves:** Equivalence of programs with different register allocation and instruction scheduling

**Program 1:**
```
0: ldp x11, x10, [x0]
4: add x12, x10, #1
8: mul x12, x11, x12
c: str x12, [x1]
```
Computes: `(x10 + 1) * x11`

**Program 2:**
```
0: ldp x21, x20, [x0]    // Different registers!
4: mul x22, x21, x20     // Reordered computation!
8: add x22, x22, x21
c: str x22, [x1]
```
Computes: `x20 * x21 + x21 = x21 * (x20 + 1)` (mathematically equivalent)

**New infrastructure:**
- **Equivalence statement builder:**
  - `mk_equiv_statement_simple assumption eqin eqout mc1 frame1 mc2 frame2`
  - Automatically constructs `ensures2` goal
  - `eqin : definition` - input state equivalence predicate
  - `eqout : definition` - output state equivalence predicate
  - Example: `eqin (s1,s1') inbuf outbuf ↔ read X0 s1 = inbuf ∧ ... ∧ ∃n. bignum_from_memory(inbuf,2) s1 = n ∧ ...`
- **Equivalence tactics:**
  - `EQUIV_INITIATE_TAC eqin` - initialize with input equivalence
  - `EQUIV_STEPS_TAC actions EXEC1 EXEC2` - symbolic execution with actions
  - **Actions list:** `[("equal",i1,j1,i2,j2); ("replace",i1,j1,i2,j2); ...]`
    - `("equal",i1,j1,i2,j2)` - instructions [i1,j1) and [i2,j2) must produce equal outputs
      - Uses lock-step simulation
      - Automatically tries to prove word equations like `x*(y+1) = x*y + x`
    - `("replace",i1,j1,i2,j2)` - instructions differ, use stuttering
  - Tools: `tools/gen-actions.py` can generate actions from assembly diff

**Word simplification:**
- `extra_word_CONV` - extensible word equation solver
- Can be extended: `extra_word_CONV := (GEN_REWRITE_CONV I [thm])::(!extra_word_CONV)`

**Key insight:** Automated diff-based equivalence checking; handles different register names

---

### 10. `rel_reordertac.ml`

**What it proves:** Equivalence when instructions are reordered

**Program 1:**
```
0: ldr x10, [x0]
4: add x10, x10, #1
8: str x10, [x1]
c: ldr x10, [x0, #8]
10: add x10, x10, #2
14: str x10, [x1, #8]
```

**Program 2 (reordered):**
```
0: ldr x10, [x0]       // Same
4: ldr x11, [x0, #8]   // MOVED UP
8: add x10, x10, #1    // Moved down
c: add x11, x11, #2    // Moved down
10: str x10, [x1]      // Moved down
14: str x11, [x1, #8]  // Same
```

**Reordering is valid if:** [x0, x0+16) and [x1, x1+16) don't overlap

**New infrastructure:**
- **Instruction mapping:** `inst_map = [1; 4; 2; 5; 3; 6]`
  - Maps instruction indices from program 2 to program 1
  - Program 2 instruction i corresponds to program 1 instruction `inst_map[i]`
- **Abbreviation tactics:**
  - `state_to_abbrevs : (int * thm) list ref` - stores abbreviations
  - `ARM_N_STEPS_AND_ABBREV_TAC EXEC (1--n) state_to_abbrevs None`
    - Execute left program
    - For each output register/memory, create abbreviation `abbrev_s<i>_<reg> = <expr>`
    - Store mapping in `state_to_abbrevs`
  - `ARM_N_STEPS_AND_REWRITE_TAC EXEC (1--n) inst_map state_to_abbrevs None`
    - Execute right program
    - For each instruction i, find corresponding abbreviation from `inst_map[i]`
    - Rewrite output using abbreviation (proves outputs match)

**Note:** May show "tactic is not VALID" during interactive proof (expected); full proof still works

**Key insight:** Prove equivalence of optimized code that reorders independent instructions

---

### 11. `rel_loop.ml`

**What it proves:** Equivalence of two loops with different instruction counts per iteration

**Program 1:** (3 instructions per iteration)
```
loop1:
0: add x2, x2, #2
4: add x0, x0, #1
8: cmp x0, x1
c: b.ne loop1
```

**Program 2:** (4 instructions per iteration)
```
loop2:
0: add x2, x2, #1
4: add x2, x2, #1
8: add x0, x0, #1
c: cmp x0, x1
10: b.ne loop2
```

**Proves:** If x0=0, x1=n, x2 starts equal, then x2 ends equal (both add 2n to x2)

**New infrastructure:**
- **Relational loop invariant:**
  - `ENSURES2_WHILE_PAUP_TAC start end pc1_body pc1_backedge pc2_body pc2_backedge inv cond1 cond2 step1 step2 ...`
  - `inv : num → state → state → bool` - relates loop counter to both states
  - `cond1, cond2 : num → state → bool` - backedge conditions
  - `step1, step2 : num → num` - step count per iteration
- **Proof obligations:**
  1. Number of iterations > 0
  2. Pre-loop (trivial `ensures2`)
  3. **Loop body** (main proof - preserve relational invariant)
  4. **Backedge** (decide whether to continue)
  5. Post-loop (trivial `ensures2`)
  6. Total step count for program 1
  7. Total step count for program 2

**Tactics used:**
- `MATCH_MP_TAC ENSURES2_TRIVIAL` - trivial ensures2 (identity)
- `FORALL_PAIR_THM` - rewrite ∀(s1,s2) to ∀s1 s2

**Key insight:** Prove loop equivalence even when iterations have different instruction counts

---

### 12. `rel_veceq.ml` - ADVANCED

**What it proves:** Scalar vs SIMD equivalence for 128×128→256-bit squaring

**Program 1 (scalar):** 13 instructions
```
0:  ldp x10, x11, [x1]
4:  mul x20, x10, x10     // x10²
8:  umulh x12, x10, x10   // high(x10²)
c:  mul x13, x10, x11     // x10*x11
10: umulh x14, x10, x11   // high(x10*x11)
14: mul x15, x11, x11     // x11²
18: umulh x16, x11, x11   // high(x11²)
1c: adds x27, x12, x13
20: adcs x28, x15, x14
24: adc x29, x16, xzr
28: adds x21, x27, x13
2c: adcs x22, x28, x14
30: adc x23, x29, xzr
```
Computes 256-bit result: `(x23:x22:x21:x20) = (x11:x10)²`

**Program 2 (SIMD):** 26 instructions using NEON
```
(Uses Q registers, vector multiply, etc.)
```
Same result but with vectorization

**Instructions (SIMD/NEON):** ⭐ ALL NEW
- `LDR Q30, [X1]` - load 128-bit vector
- `UMULL Q0, Q30, Q30, 32` - vector unsigned multiply low
- `UMULL2 Q2, Q30, Q30, 32` - vector unsigned multiply high
- `XTN Q24, Q30, 32` - extract narrow
- `UZP2 Q30, Q30, Q30, 32` - unzip vectors
- `UMOV X7, Q0, 0, 8` - move vector element to GPR
- `EXTR X4, X12, X4, 63` - extract bits

**New infrastructure:**
- **NEON support:**
  - `needs "arm/proofs/neon_helper.ml"` - SIMD lemmas and tactics
  - Vector register state (Q0-Q31)
  - Vector instruction semantics
- **Advanced word simplification:**
  - `WORD_BITMANIP_SIMP_LEMMAS` - bit manipulation rules
  - `WORD_SQR128_DIGIT0/1/2/3` - squaring lemmas for 128-bit values
  - Custom rewrite rules added to `extra_word_CONV`
  - Sometimes need `RULE_ASSUM_TAC (REWRITE_RULE[...])` manually

**Tactics used:**
- `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` - ABI-compliant register changes
- Standard relational tactics from previous tutorials

**Key insight:** Real-world optimization verification; significant effort in word lemmas

**Status:** "Dirty" proof - not fully clean, manual rewrites needed, but demonstrates feasibility

---

## Infrastructure Implementation Priority

Based on tutorial progression, implement in this order:

### Phase 1-2: Foundation (Tutorials 2-3)
1. MOV, MUL instructions
2. ENSURES_SEQUENCE_TAC
3. .o file parser (basic)
4. CMP, conditional branches (B.HI, B.NE)
5. RET instruction
6. Flag handling (SOME_FLAGS)
7. COND_CASES_TAC equivalent

### Phase 3-4: Memory and Loops (Tutorials 4-5)
8. LDR, STR instructions
9. Memory model (bytes64, nonoverlapping)
10. MAYCHANGE memory tracking
11. MOV from XZR
12. ENSURES_WHILE_PAUP_TAC
13. Loop invariants

### Phase 5-6: Bignum and Data (Tutorials 6-7)
14. LDP instruction
15. bignum_from_memory abstraction
16. BIGNUM_DIGITIZE_TAC
17. Full .o parser (define_assert_from_elf)
18. ADRP, ADD immediate, B
19. LDR with shifted offset
20. Relocation parser (define_assert_relocs_from_elf)
21. ARM_SUBROUTINE_SIM_TAC

### Phase 7-11: Relational Reasoning (Tutorials 8-12)
22. ensures2 framework
23. ENSURES2_INIT_TAC, stuttering tactics
24. mk_equiv_statement_simple
25. EQUIV_STEPS_TAC with actions
26. Abbreviation tactics
27. ENSURES2_WHILE_PAUP_TAC
28. NEON/SIMD instructions (ambitious!)

---

## Key Observations

1. **Incremental complexity:** Each tutorial builds on previous infrastructure
2. **Instruction coverage:** ~25 unique instructions across all tutorials
3. **Tactic development:** ~15 major tactics needed
4. **Memory model:** Evolves from simple register state → memory → multi-word → PC-relative data
5. **Proof patterns:** Linear → compositional → conditional → loops → functions → equivalence
6. **Relational reasoning:** Completely separate framework (ensures2) built on top of unary (ensures)
7. **Realistic verification:** Tutorial 12 shows complexity of real optimization verification

## Next Steps for Lean Port

**Immediate (Phase 1):**
- Implement MOV, MUL instruction semantics
- Port ENSURES_SEQUENCE_TAC to Lean
- Build basic .o file parser (can start with hardcoded bytecode)

**Short-term (Phases 2-3):**
- Conditional branch infrastructure
- Memory operation infrastructure
- Start building tactic library

**Medium-term (Phases 4-6):**
- Loop invariant reasoning
- Bignum abstractions
- Function call support

**Long-term (Phases 7-11):**
- Full relational reasoning framework
- Advanced optimizations
- SIMD (if needed)
