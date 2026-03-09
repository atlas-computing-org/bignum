/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

/-!
# 64-bit Word Arithmetic

This file defines 64-bit words and foundational theorems,
corresponding to the word operations in HOL Light.

## Main Definitions

* `Word64` - 64-bit words (alias for BitVec 64)

## References

Source: HOL Light's Library/words.ml
Related: s2n-bignum/common/bignum.ml (VAL_WORD_BIGDIGIT, etc.)
-/

@[expose] public section

namespace Bignum

/--
A 64-bit word, represented as a bitvector.
-/
public abbrev Word64 := BitVec 64

/--
The value of a word constructed from a natural number that's already
bounded by 2^64 equals that natural number.

Corresponds to HOL Light's VAL_WORD_EQ and related theorems.

Source: Related to s2n-bignum/common/bignum.ml:29-31 (VAL_WORD_BIGDIGIT)
-/
theorem val_ofNat_of_lt {n : Nat} (h : n < 2^64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]


/--
Converting to word and back gives modulo 2^64.
-/
theorem val_ofNat (n : Nat) :
    (BitVec.ofNat 64 n : Word64).toNat = n % 2^64 := by
  simp [BitVec.toNat_ofNat]

/--
Word values are always bounded by 2^64.
-/
theorem val_lt (w : Word64) : w.toNat < 2^64 := by
  exact BitVec.isLt w

end Bignum
