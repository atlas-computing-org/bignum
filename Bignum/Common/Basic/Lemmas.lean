/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
import Bignum.Common.Basic.Defs
import Mathlib.Data.Finset.Basic

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
theorem high_low_digits (n i : Nat) :
    2 ^ (64 * i) * highdigits n i + lowdigits n i = n := by
  unfold highdigits lowdigits
  exact Nat.div_add_mod n (2 ^ (64 * i))

theorem high_low_digits' (n i : Nat) :
    lowdigits n i + 2 ^ (64 * i) * highdigits n i = n := by
  rw [Nat.add_comm]
  exact high_low_digits n i

/--
Recursive characterization of highdigits.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_CLAUSES = prove
 (`(!n. highdigits n 0 = n) /\
   (!n i. highdigits n (i + 1) = highdigits n i DIV 2 EXP 64)`, ...);;
```

Source: s2n-bignum/common/bignum.ml:87-91
-/
theorem highdigits_succ (n i : Nat) :
    highdigits n (i + 1) = highdigits n i / 2 ^ 64 := by
  unfold highdigits
  sorry -- TODO: complete proof

/--
Step theorem: relating highdigits at position i with i+1 and the digit at i.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_STEP = prove
 (`!n i. highdigits n i = 2 EXP 64 * highdigits n (i + 1) + bigdigit n i`, ...);;
```

Source: s2n-bignum/common/bignum.ml:93-96
-/
theorem highdigits_step (n i : Nat) :
    highdigits n i = 2 ^ 64 * highdigits n (i + 1) + bigdigit n i := by
  unfold highdigits bigdigit
  sorry -- TODO: complete proof

/--
Recursive characterization of lowdigits.

Corresponds to HOL Light theorem:
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
  sorry -- TODO: complete proof

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
  sorry -- TODO: complete proof

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
theorem bigdigitsum_works (n k : Nat) (h : n < 2 ^ (64 * k)) :
    (Finset.range k).sum (fun i => 2 ^ (64 * i) * bigdigit n i) = n := by
  sorry -- TODO: complete proof

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
  sorry -- TODO: complete proof

end Bignum
