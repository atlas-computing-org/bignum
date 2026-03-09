/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

/-!
# 64-bit Word Arithmetic

This file defines 64-bit words and their arithmetic operations,
corresponding to the word operations in HOL Light.

## Main Definitions

* `Word64` - 64-bit words (alias for BitVec 64)
* `val` - Convert word to natural number
* `word` - Convert natural number to word (with modulo)

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
Convert a Word64 to a natural number.

Corresponds to HOL Light's `val : (N)word -> num`
-/
public def Word64.val (w : Word64) : Nat :=
  w.toNat

/--
Convert a natural number to a Word64 (with implicit modulo 2^64).

Corresponds to HOL Light's `word : num -> (N)word`
-/
public def Word64.ofNat (n : Nat) : Word64 :=
  BitVec.ofNat 64 n


/--
The value of a word constructed from a natural number that's already
bounded by 2^64 equals that natural number.

Corresponds to HOL Light's VAL_WORD_EQ and related theorems.

Source: Related to s2n-bignum/common/bignum.ml:29-31 (VAL_WORD_BIGDIGIT)
-/
theorem val_ofNat_of_lt {n : Nat} (h : n < 2^64) :
    (Word64.ofNat n).val = n := by
  unfold Word64.ofNat Word64.val
  grind only [= BitVec.toNat_ofNat]


/--
Converting to word and back gives modulo 2^64.
-/
theorem val_ofNat (n : Nat) :
    (Word64.ofNat n).val = n % 2^64 := by
  unfold Word64.ofNat Word64.val
  simp [BitVec.toNat_ofNat]

/--
Word values are always bounded by 2^64.
-/
theorem val_lt (w : Word64) : w.val < 2^64 := by
  unfold Word64.val
  have := BitVec.isLt w
  simp at this
  exact this

end Bignum
