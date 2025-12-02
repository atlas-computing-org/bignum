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
* Arithmetic operations with carry/borrow

## References

Source: HOL Light's Library/words.ml
Related: s2n-bignum/common/bignum.ml (VAL_WORD_BIGDIGIT, etc.)
-/

namespace Bignum

/--
A 64-bit word, represented as a bitvector.
-/
abbrev Word64 := BitVec 64

/--
Convert a Word64 to a natural number.

Corresponds to HOL Light's `val : (N)word -> num`
-/
def Word64.val (w : Word64) : ℕ := w.toNat

/--
Convert a natural number to a Word64 (with implicit modulo 2^64).

Corresponds to HOL Light's `word : num -> (N)word`
-/
def Word64.ofNat (n : ℕ) : Word64 := BitVec.ofNat 64 n

/--
Word addition with carry out.

Returns (sum, carry) where:
- sum = (x + y) % 2^64
- carry = 1 if x + y >= 2^64, else 0

This models the ARM ADDS instruction behavior.
-/
def Word64.addWithCarry (x y : Word64) : Word64 × ℕ :=
  let sum := x.val + y.val
  (Word64.ofNat sum, if sum >= 2^64 then 1 else 0)

/--
Word addition with carry in and carry out.

Returns (sum, carry_out) where:
- sum = (x + y + carry_in) % 2^64
- carry_out = 1 if x + y + carry_in >= 2^64, else 0

This models the ARM ADCS instruction behavior.
-/
def Word64.adcWithCarry (x y : Word64) (carry_in : ℕ) : Word64 × ℕ :=
  let sum := x.val + y.val + carry_in
  (Word64.ofNat sum, if sum >= 2^64 then 1 else 0)

/--
Word subtraction with borrow out.

Returns (diff, borrow) where:
- diff = (x - y) % 2^64
- borrow = 1 if x < y, else 0

This models the ARM SUBS instruction behavior.
-/
def Word64.subWithBorrow (x y : Word64) : Word64 × ℕ :=
  let diff := x.val - y.val
  (Word64.ofNat diff, if x.val < y.val then 1 else 0)

/--
Word subtraction with borrow in and borrow out.

Returns (diff, borrow_out) where:
- diff = (x - y - borrow_in) % 2^64
- borrow_out = 1 if x < y + borrow_in, else 0

This models the ARM SBCS instruction behavior.
-/
def Word64.sbcWithBorrow (x y : Word64) (borrow_in : ℕ) : Word64 × ℕ :=
  let diff := x.val - y.val - borrow_in
  (Word64.ofNat diff, if x.val < y.val + borrow_in then 1 else 0)

/--
The value of a word constructed from a natural number that's already
bounded by 2^64 equals that natural number.

Corresponds to HOL Light's VAL_WORD_EQ and related theorems.

Source: Related to s2n-bignum/common/bignum.ml:29-31 (VAL_WORD_BIGDIGIT)
-/
theorem val_ofNat_of_lt {n : ℕ} (h : n < 2^64) :
    (Word64.ofNat n).val = n := by
  unfold Word64.ofNat Word64.val
  simp [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/--
Converting to word and back gives modulo 2^64.
-/
theorem val_ofNat (n : ℕ) :
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
