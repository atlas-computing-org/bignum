/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

@[expose] public section

/-!
# Basic Bignum Definitions

This file contains the fundamental definitions for bignums in Lean,
ported from s2n-bignum/common/bignum.ml

## Main Definitions

* `bigdigit n i` - Extracts the i-th 64-bit digit from natural number n
* `highdigits n i` - Returns the high part: n DIV (2^(64*i))
* `lowdigits n i` - Returns the low part: n MOD (2^(64*i))

## References

Source: s2n-bignum/common/bignum.ml (lines 11-77)
-/

namespace Bignum

/--
Extract the i-th 64-bit digit from a natural number n.

This corresponds to HOL Light's definition:
```ocaml
let bigdigit = new_definition
 `bigdigit n i = (n DIV (2 EXP (64 * i))) MOD (2 EXP 64)`;;
```

Source: s2n-bignum/common/bignum.ml:11-12
-/
def bigdigit (n : Nat) (i : Nat) : Nat :=
  (n / (2 ^ (64 * i))) % (2 ^ 64)


/--
Extract the high digits of n starting from position i.
Essentially n DIV (2^(64*i)).

This corresponds to HOL Light's definition:
```ocaml
let highdigits = new_definition
 `highdigits n i = n DIV (2 EXP (64 * i))`;;
```

Source: s2n-bignum/common/bignum.ml:73-74
-/
def highdigits (n : Nat) (i : Nat) : Nat :=
  n / (2 ^ (64 * i))

/--
Extract the low digits of n up to position i.
Essentially n MOD (2^(64*i)).

This corresponds to HOL Light's definition:
```ocaml
let lowdigits = new_definition
 `lowdigits n i = n MOD (2 EXP (64 * i))`;;
```

Source: s2n-bignum/common/bignum.ml:76-77
-/
def lowdigits (n : Nat) (i : Nat) : Nat :=
  n % (2 ^ (64 * i))


/--
A bigdigit is always less than 2^64.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_BOUND = prove
 (`!n i. bigdigit n i < 2 EXP 64`, ...);;
```

Source: s2n-bignum/common/bignum.ml:24-27
-/
theorem bigdigit_bound (n i : Nat) : bigdigit n i < 2 ^ 64 := by
  unfold bigdigit
  apply Nat.mod_lt
  decide


/--
bigdigit of 0 is always 0.

Corresponds to HOL Light theorem:
```ocaml
let BIGDIGIT_0 = prove
 (`!i. bigdigit 0 i = 0`, ...);;
```

Source: s2n-bignum/common/bignum.ml:33-35
-/
theorem bigdigit_zero (i : Nat) : bigdigit 0 i = 0 := by
  unfold bigdigit
  simp

/--
lowdigits of 0 is always 0.

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_0 = prove
 (`!n. lowdigits n 0 = 0`, ...);;
```

Source: s2n-bignum/common/bignum.ml:121-123
-/
theorem lowdigits_zero (n : Nat) : lowdigits n 0 = 0 := by
  unfold lowdigits
  rw [Nat.mul_zero, Nat.pow_zero]
  exact Nat.mod_one n

/--
highdigits of n at position 0 is n itself.

Corresponds to HOL Light theorem:
```ocaml
let HIGHDIGITS_0 = prove
 (`!n. highdigits n 0 = n`, ...);;
```

Source: s2n-bignum/common/bignum.ml:109-111
-/
theorem highdigits_zero (n : Nat) : highdigits n 0 = n := by
  unfold highdigits
  simp

/--
lowdigits is always bounded by 2^(64*i).

Corresponds to HOL Light theorem:
```ocaml
let LOWDIGITS_BOUND = prove
 (`!n i. lowdigits n i < 2 EXP (64 * i)`, ...);;
```

Source: s2n-bignum/common/bignum.ml:139-141
-/
theorem lowdigits_bound (n i : Nat) : lowdigits n i < 2 ^ (64 * i) := by
  unfold lowdigits
  exact Nat.mod_lt _ (Nat.two_pow_pos (64 * i))

end Bignum
