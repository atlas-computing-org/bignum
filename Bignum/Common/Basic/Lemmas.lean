/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Common.Basic.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.Group.Basic

@[expose] public section

/-!
# Basic Bignum Lemmas

Fundamental theorems about bignum operations, ported from s2n-bignum/common/bignum.ml

## Main Theorems

* `high_low_digits` - Decomposition: n = 2^(64*i) * highdigits n i + lowdigits n i
* `highdigits_clauses` - Recursive characterization of highdigits
* `lowdigits_clauses` - Recursive characterization of lowdigits
* `bigdigitsum_works` - Sum of digits equals the number (when bounded)

## References

Source: s2n-bignum/common/bignum.ml (lines 79-150)
-/

namespace Bignum

/--
Fundamental decomposition theorem: any number can be split into high and low parts.

Corresponds to HOL Light theorem:
```ocaml
let HIGH_LOW_DIGITS = prove
 (`(!n i. 2 EXP (64 * i) * highdigits n i + lowdigits n i = n) /\
   (!n i. lowdigits n i + 2 EXP (64 * i) * highdigits n i = n) /\
   (!n i. highdigits n i * 2 EXP (64 * i) + lowdigits n i = n) /\
   (!n i. lowdigits n i + highdigits n i * 2 EXP (64 * i) = n)`, ...);;
```

Source: s2n-bignum/common/bignum.ml:79-85
-/
theorem high_low_digits (n i : Nat)
  : 2 ^ (64 * i) * highdigits n i + lowdigits n i = n := by
  unfold highdigits lowdigits
  exact Nat.div_add_mod n (2 ^ (64 * i))


/--
Recursive characterization of highdigits. This is the **second clause** of HOL
Light's `HIGHDIGITS_CLAUSES`. The first clause (`highdigits n 0 = n`) is in
Defs.lean as `highdigits_zero`.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_CLAUSES = prove
 (`(!n. highdigits n 0 = n) /\  -- clause 1
   (!n i. highdigits n (i + 1) = highdigits n i DIV 2 EXP 64)`, ...);; -- clause 2
```

Source: s2n-bignum/common/bignum.ml:87-91 (HIGHDIGITS_CLAUSES, clause 2)
-/
theorem highdigits_succ (n i : Nat) :
    highdigits n (i + 1) = highdigits n i / 2 ^ 64 := by
  unfold highdigits
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.pow_add]
  rw [Nat.div_div_eq_div_mul]


/--
Step theorem: relating highdigits at position i with i+1 and the digit at i.

This is a key decomposition theorem: highdigits at position i equals
the highdigits at i+1 (shifted left by 64 bits) plus the digit at position i.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_STEP = prove
 (`!n i. highdigits n i = 2 EXP 64 * highdigits n (i + 1) + bigdigit n i`,
  REWRITE_TAC[highdigits; bigdigit; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN ARITH_TAC);;
```

Source: s2n-bignum/common/bignum.ml:93-96
-/
theorem highdigits_step (n i : Nat) :
    highdigits n i = 2 ^ 64 * highdigits n (i + 1) + bigdigit n i := by
  unfold highdigits bigdigit
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  omega


/-- Helper lemma: modular arithmetic with multiplication -/
private lemma mod_mul_add_mod (q r d m : Nat) (hr : r < d) (hm : 0 < m) :
    (q * d + r) % (d * m) = d * (q % m) + r := by
  -- Write q using Euclidean division: q = (q/m)*m + (q%m)
  have q_div : q = q / m * m + q % m := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod q m).symm
  calc (q * d + r) % (d * m)
      = ((q / m * m + q % m) * d + r) % (d * m) := by rw [← q_div]
    _ = ((q / m * m) * d + (q % m) * d + r) % (d * m) := by ring_nf
    _ = (q / m * m * d + ((q % m) * d + r)) % (d * m) := by ring_nf
    _ = (q / m * (m * d) + ((q % m) * d + r)) % (d * m) := by rw [Nat.mul_assoc]
    _ = (q / m * (d * m) + ((q % m) * d + r)) % (d * m) := by rw [Nat.mul_comm m d]
    _ = (((q % m) * d + r) + q / m * (d * m)) % (d * m) := by rw [Nat.add_comm]
    _ = ((q % m) * d + r) % (d * m) := by rw [Nat.add_mul_mod_self_right]
    _ = d * (q % m) + r := by
      -- Show (q%m)*d + r < d*m
      have bound : (q % m) * d + r < d * m := by
        have qm_lt : q % m < m := Nat.mod_lt q hm
        calc (q % m) * d + r
            < (q % m) * d + d := Nat.add_lt_add_left hr _
          _ ≤ (m - 1) * d + d :=
            Nat.add_le_add_right (Nat.mul_le_mul_right d (Nat.le_pred_of_lt qm_lt)) _
          _ = ((m - 1) + 1) * d := by ring
          _ = m * d := by rw [Nat.sub_add_cancel (Nat.one_le_of_lt hm)]
          _ = d * m := Nat.mul_comm m d
      rw [Nat.mod_eq_of_lt bound, Nat.mul_comm]

/--
Recursive characterization of lowdigits. This is the **second clause** of HOL
Light's `LOWDIGITS_CLAUSES`. Corresponds to HOL Light theorem:

```ocaml
let LOWDIGITS_CLAUSES = prove
 (`(!n. lowdigits n 0 = 0) /\
   (!n i. lowdigits n (i + 1) =
          2 EXP (64 * i) * bigdigit n i + lowdigits n i)`, ...);;
```

Source: s2n-bignum/common/bignum.ml:98-103
-/
theorem lowdigits_succ (n i : Nat) :
    lowdigits n (i + 1) = 2 ^ (64 * i) * bigdigit n i + lowdigits n i := by
  unfold lowdigits bigdigit
  simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  -- Apply the helper lemma
  have h₁ := mod_mul_add_mod (n / 2 ^ (64 * i)) (n % 2 ^ (64 * i))
    (2 ^ (64 * i)) (2 ^ 64)
    (Nat.mod_lt n (Nat.two_pow_pos (64 * i)))
    (Nat.two_pow_pos 64)
  -- Rewrite goal using Euclidean division
  conv_lhs => arg 1; rw [← Nat.div_add_mod n (2 ^ (64 * i)), Nat.mul_comm]
  exact h₁

/--
highdigits equals 0 iff n is bounded.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_EQ_0 = prove
 (`!n i. highdigits n i = 0 <=> n < 2 EXP (64 * i)`, ...);;
```

Source: s2n-bignum/common/bignum.ml:105-107
-/
theorem highdigits_eq_zero (n i : Nat) :
    highdigits n i = 0 ↔ n < 2 ^ (64 * i) := by
  unfold highdigits
  apply Iff.intro
  repeat simp


/--
If n is bounded, then highdigits n i = 0.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_ZERO = prove
 (`!n i. n < 2 EXP (64 * i) ==> highdigits n i = 0`, ...);;
```

Source: s2n-bignum/common/bignum.ml:113-115
-/
theorem highdigits_of_lt (n i : Nat) (h : n < 2 ^ (64 * i)) :
    highdigits n i = 0 := by
  rw [highdigits_eq_zero]
  exact h


/--
If n is bounded, the top digit equals highdigits at position k-1.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_TOP = prove
 (`!n k. n < 2 EXP (64 * k) ==> highdigits n (k - 1) = bigdigit n (k - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[highdigits; bigdigit] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;
```

Source: s2n-bignum/common/bignum.ml:131-137
-/
theorem highdigits_top (n k : Nat) (h : n < 2 ^ (64 * k)) :
    highdigits n (k - 1) = bigdigit n (k - 1) := by
  unfold highdigits bigdigit
  sorry


/--
highdigits of 0 is always 0.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_TRIVIAL = prove
 (`!n. highdigits 0 n = 0`,
  REWRITE_TAC[highdigits; DIV_0]);;
```

Source: s2n-bignum/common/bignum.ml:117-119
-/
theorem highdigits_trivial (n : Nat) :
    highdigits 0 n = 0 := by
  unfold highdigits
  simp


/--
Compositionality of highdigits: taking highdigits twice is equivalent to adding indices.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_HIGHDIGITS = prove
 (`!n i j. highdigits (highdigits n i) j = highdigits n (i + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[highdigits] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; DIV_DIV]);;
```

Source: s2n-bignum/common/bignum.ml:169-172
-/
theorem highdigits_highdigits (n i j : Nat) :
    highdigits (highdigits n i) j = highdigits n (i + j) := by
  unfold highdigits
  rw [Nat.mul_add, Nat.pow_add, Nat.div_div_eq_div_mul]


/--
If n is bounded, then lowdigits n i = n.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_SELF = prove
 (`!n i. n < 2 EXP (64 * i) ==> lowdigits n i = n`, ...);;
```

Source: s2n-bignum/common/bignum.ml:147-149
-/
theorem lowdigits_of_lt (n i : Nat) (h : n < 2 ^ (64 * i)) :
    lowdigits n i = n := by
  unfold lowdigits
  exact Nat.mod_eq_of_lt h


/--
The first lowdigit equals the 0-th bigdigit.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_1 = prove
 (`!n. lowdigits n 1 = bigdigit n 0`,
  SUBST1_TAC(ARITH_RULE `1 = 0 + 1`) THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; LOWDIGITS_0] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES]);;
```

Source: s2n-bignum/common/bignum.ml:125-129
-/
theorem lowdigits_one (n : Nat) :
    lowdigits n 1 = bigdigit n 0 := by
  rw [lowdigits_succ, lowdigits_zero]
  grind


/--
lowdigits of 0 is always 0.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_TRIVIAL = prove
 (`!n. lowdigits 0 n = 0`,
  REWRITE_TAC[lowdigits; MOD_0]);;
```

Source: s2n-bignum/common/bignum.ml:151-153
-/
theorem lowdigits_trivial (n : Nat) :
    lowdigits 0 n = 0 := by
  unfold lowdigits
  simp


/--
lowdigits equals n iff n is bounded.

This is the bidirectional version of `lowdigits_of_lt`.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_EQ_SELF = prove
 (`!n i. lowdigits n i = n <=> n < 2 EXP (64 * i)`,
  SIMP_TAC[lowdigits; MOD_EQ_SELF; EXP_EQ_0; ARITH_EQ]);;
```

Source: s2n-bignum/common/bignum.ml:143-145
-/
theorem lowdigits_eq_self (n i : Nat) :
    lowdigits n i = n ↔ n < 2 ^ (64 * i) := by
  unfold lowdigits
  constructor
  · intro h
    rw [← h]
    exact Nat.mod_lt n (Nat.two_pow_pos (64 * i))
  · exact Nat.mod_eq_of_lt


/--
lowdigits is always less than or equal to the original number.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_LE = prove
 (`!n i. lowdigits n i <= n`,
  REWRITE_TAC[lowdigits; MOD_LE]);;
```

Source: s2n-bignum/common/bignum.ml:155-157
-/
theorem lowdigits_le (n i : Nat) :
    lowdigits n i ≤ n := by
  unfold lowdigits
  exact Nat.mod_le n (2 ^ (64 * i))


/--
Compositionality of lowdigits: taking lowdigits twice equals taking the minimum.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_LOWDIGITS = prove
 (`!n i j. lowdigits (lowdigits n i) j = lowdigits n (MIN i j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lowdigits; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
```

Source: s2n-bignum/common/bignum.ml:159-162
-/
theorem lowdigits_lowdigits (n i j : Nat) :
    lowdigits (lowdigits n i) j = lowdigits n (min i j) := by
  unfold lowdigits
  sorry


/--
If n is bounded by 2^(64*k), then the sum of its digits equals n.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGITSUM_WORKS = prove
 (`!n k. n < 2 EXP (64 * k)
         ==> nsum {i | i < k} (\i. 2 EXP (64 * i) * bigdigit n i) = n`, ...);;
```

Source: s2n-bignum/common/bignum.ml:19-22

Note: We use Finset.sum instead of HOL Light's nsum.
-/
theorem bigdigitsum_works (n k : Nat) (h : n < 2 ^ (64 * k))
 : (Finset.range k).toList.foldl (init := 0)
   (fun i => 2 ^ (64 * i) * bigdigit n i) = n := by
  sorry


/--
If a number is less than 2^(64*i), then its i-th bigdigit is 0.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_ZERO = prove
 (`!n i. n < 2 EXP (64 * i) ==> bigdigit n i = 0`, ...);;
```

Source: s2n-bignum/common/bignum.ml:37-39
-/
theorem bigdigit_of_lt (n i : Nat) (h : n < 2 ^ (64 * i)) :
    bigdigit n i = 0 := by
  unfold bigdigit
  grind [Nat.div_eq_zero_iff]


/--
bigdigit is unaffected by adding a high-order term.

If we add a term `2^(64*n) * b` to `a`, the digits below position `n` remain unchanged.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_ADD_LEFT =
  prove(`forall a n b i.
  i < n ==> bigdigit (a + 2 EXP (64 * n) * b) i = bigdigit a i`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit] THEN
  SUBGOAL_THEN `2 EXP (64 * n) = 2 EXP (64 * i) * (2 EXP (64 * (n-i)))` SUBST_ALL_TAC THENL [
    REWRITE_TAC[GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; EXP_2_NE_0] THEN
    SUBGOAL_THEN
      `2 EXP (64*(n-i)) = 2 EXP 64 * (2 EXP (64*(n-i-1)))`
      SUBST_ALL_TAC THENL [
      REWRITE_TAC[GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;

      ALL_TAC
    ] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    IMP_REWRITE_TAC[MOD_MULT_ADD; EXP_2_NE_0]]);;
```

Source: s2n-bignum/common/bignum.ml:41-62
-/
theorem bigdigit_add_left (a n b i : Nat) (h : i < n) :
    bigdigit (a + 2 ^ (64 * n) * b) i = bigdigit a i := by
  unfold bigdigit
  sorry


/--
Successor digit extraction: extracting digit (i+1) from a 2-word number.

When a number is written as `t + 2^64 * n` where `t < 2^64`,
the digit at position (i+1) equals the digit at position i of n.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_SUC = prove(`forall n i t.
  t < 2 EXP 64 ==> bigdigit (t + 2 EXP 64 * n) (SUC i) = bigdigit n i`,

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit;ARITH_RULE`SUC i = 1 + i`;LEFT_ADD_DISTRIB;EXP_ADD;GSYM DIV_DIV;
              ARITH_RULE`64 * 1 = 64`] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD;EXP_2_NE_0;SPECL [`t:num`;`2 EXP 64`] DIV_LT] THEN
  REWRITE_TAC[ADD]);;
```

Source: s2n-bignum/common/bignum.ml:64-71
-/
theorem bigdigit_succ (n i t : Nat) (h : t < 2 ^ 64) :
    bigdigit (t + 2 ^ 64 * n) (i + 1) = bigdigit n i := by
  unfold bigdigit
  sorry


/--
Compositionality: bigdigit of highdigits shifts indices.

Extracting digit j from highdigits at position i is the same as extracting
digit (i+j) from the original number.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_HIGHDIGITS = prove
 (`!n i j. bigdigit (highdigits n i) j = bigdigit n (i + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; highdigits] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; DIV_DIV]);;
```

Source: s2n-bignum/common/bignum.ml:164-167
-/
theorem bigdigit_highdigits (n i j : Nat) :
    bigdigit (highdigits n i) j = bigdigit n (i + j) := by
  unfold bigdigit highdigits
  rw [Nat.mul_add, Nat.pow_add, Nat.div_div_eq_div_mul]


/--
Extracting digits from lowdigits: only digits below position i are preserved.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_LOWDIGITS = prove
 (`!n i j. bigdigit (lowdigits n i) j = if j < i then bigdigit n j else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; lowdigits] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `j < i ==> MIN (64 * i) (64 * j + 64) = 64 * j + 64`];
    MATCH_MP_TAC(MESON[MOD_0] `x = 0 ==> x MOD n = 0`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (64 * i)` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC]);;
```

Source: s2n-bignum/common/bignum.ml:174-184
-/
theorem bigdigit_lowdigits (n i j : Nat) :
    bigdigit (lowdigits n i) j = if j < i then bigdigit n j else 0 := by
  unfold bigdigit lowdigits
  sorry

end Bignum
