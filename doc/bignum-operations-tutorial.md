# Tutorial: Bignum Operations

This document provides educational examples of how the functions
`bigdigit`, `highdigits` and `lowdigits` work in practice.

## Word Order: Little-Endian

**IMPORTANT:** The implementation uses **little-endian at the word level**:

- **Word 0** (lower index)  = **least** significant bits (0-63)
- **Word 1**                = bits 64-127
- **Word 2** (higher index) = **most** significant bits (128-191)

This means: `n = word[0] * 2^0 + word[1] * 2^64 + word[2] * 2^128 + ...`

---

## Example: 192-bit Number (3 words of 64 bits)

Let's use a concrete number:
```
n = 1 * 2^128 + 5 * 2^64 + 7 * 1
n = [ 0x0000000000000001 , 0x0000000000000005 , 0x0000000000000007 ]
```

**Visual representation (memory order, little-endian):**

```
Increasing addresses →
┌──────────────┬──────────────┬──────────────┐
│ word 0       │ word 1       │ word 2       │  ← indices
│ (bits 0-63)  │ (bits 64-127)│ (bits 128+)  │
│ least signif │              │ most signif  │
├──────────────┼──────────────┼──────────────┤
│      7       │      5       │      1       │  ← values
└──────────────┴──────────────┴──────────────┘

Value: n = 7 * 2^0 + 5 * 2^64 + 1 * 2^128
```

### 1. **bigdigit n i** - Extract the i-th 64-bit word

```lean
bigdigit n i = (n / (2^(64*i))) % (2^64)
```

**Step by step:**

```
bigdigit n 0 = (n / 2^0) % 2^64
             = n % 2^64
             = (2^128 + 5*2^64 + 7) % 2^64
             = 7                              ← word 0

bigdigit n 1 = (n / 2^64) % 2^64
             = ((2^128 + 5*2^64 + 7) / 2^64) % 2^64
             = (2^64 + 5 + 7/2^64) % 2^64
             = (2^64 + 5) % 2^64
             = 5                              ← word 1

bigdigit n 2 = (n / 2^128) % 2^64
             = ((2^128 + 5*2^64 + 7) / 2^128) % 2^64
             = (1 + 5/2^64 + 7/2^128) % 2^64
             = 1                              ← word 2

bigdigit n 3 = (n / 2^192) % 2^64
             = 0                              ← no more bits
```

**Interpretation:** `bigdigit` works as a "word selector" - returns only the word at position `i`.

---

### 2. **lowdigits n i** - Get the lowest i*64 bits

```lean
lowdigits n i = n % (2^(64*i))
```

**Step by step:**

```
lowdigits n 0 = n % 2^0
              = n % 1
              = 0                              ← no bits

lowdigits n 1 = n % 2^64
              = (2^128 + 5*2^64 + 7) % 2^64
              = 7                              ← only word 0
              ┌──────────────┐
              │ word 0: 7    │
              └──────────────┘

lowdigits n 2 = n % 2^128
              = (2^128 + 5*2^64 + 7) % 2^128
              = 5*2^64 + 7                     ← words 0 and 1
              ┌──────────────┬──────────────┐
              │ word 0: 7    │ word 1: 5    │
              └──────────────┴──────────────┘

lowdigits n 3 = n % 2^192
              = 2^128 + 5*2^64 + 7             ← words 0, 1 and 2
              ┌──────────────┬──────────────┬──────────────┐
              │ word 0: 7    │ word 1: 5    │ word 2: 1    │
              └──────────────┴──────────────┴──────────────┘
```

**Interpretation:** `lowdigits` is a "mask" that zeros all bits above position `64*i`.

---

### 3. **highdigits n i** - Shift right by i*64 bits

```lean
highdigits n i = n / (2^(64*i))
```

**Step by step:**

```
highdigits n 0 = n / 2^0
               = n / 1
               = 2^128 + 5*2^64 + 7            ← complete number
               ┌──────────────┬──────────────┬──────────────┐
               │ word 0: 7    │ word 1: 5    │ word 2: 1    │
               └──────────────┴──────────────┴──────────────┘

highdigits n 1 = n / 2^64
               = (2^128 + 5*2^64 + 7) / 2^64
               = 2^64 + 5                      ← discards word 0
               ┌──────────────┬──────────────┐
               │ word 0: 5    │ word 1: 1    │  ← reindexed!
               └──────────────┴──────────────┘

highdigits n 2 = n / 2^128
               = (2^128 + 5*2^64 + 7) / 2^128
               = 1                             ← discards words 0 and 1
               ┌──────────────┐
               │ word 0: 1    │  ← reindexed!
               └──────────────┘

highdigits n 3 = n / 2^192
               = 0                             ← discards everything
```

**Interpretation:** `highdigits` is a "right shift" of `64*i` bits, discarding the low words.

---

## Fundamental Theorem: `high_low_digits`

Now let's verify the theorem we proved:

```lean
theorem high_low_digits (n i : Nat) :
  2^(64*i) * highdigits n i + lowdigits n i = n
```

**Example with i=1:**

```
2^64 * highdigits n 1 + lowdigits n 1
  = 2^64 * (2^64 + 5) + 7                    ← substitution
  = 2^128 + 5*2^64 + 7                       ← distributive
  = n                                        ✓ Correct!
```

**Visualization:**

```
highdigits n 1:                      lowdigits n 1:
(value = 2^64 + 5)                   (value = 7)
┌──────────────┬──────────────┐      ┌──────────────┐
│ word 0: 5    │ word 1: 1    │      │ word 0: 7    │
└──────────────┴──────────────┘      └──────────────┘
         ↓                                    ↓
    2^64 * (2^64 + 5)           +             7
         ↓                                    ↓
    ┌──────────────┬──────────────┬──────────────┐
    │ word 0: 7    │ word 1: 5    │ word 2: 1    │  = n
    └──────────────┴──────────────┴──────────────┘
```

**Insight:** The number can always be decomposed into:
- **High part** (highdigits): shifted left by `64*i` bits
- **Low part** (lowdigits): the `64*i` least significant bits

This is exactly **Euclidean division**: `n = q * d + r` where:
- `q` = `highdigits n i` (quotient)
- `d` = `2^(64*i)` (divisor)
- `r` = `lowdigits n i` (remainder)

---

## Practical Example: Addition with Carry

Suppose we want to add two 128-bit numbers:

```
a = 2^64 - 1 + 2^64 * 10     (word 0 = 2^64-1, word 1 = 10)
b = 5 + 2^64 * 3             (word 0 = 5, word 1 = 3)
```

**Word-by-word addition:**

```
Word 0:
  bigdigit a 0 + bigdigit b 0  = (2^64 - 1) + 5
                               = 2^64 + 4
                               = 4  (mod 2^64)  with carry = 1

Word 1:
  bigdigit a 1 + bigdigit b 1 + carry = 10 + 3 + 1
                                      = 14  (no carry)

Result:
  ┌──────────────┬──────────────┐
  │ word 0: 4    │ word 1: 14   │
  └──────────────┴──────────────┘
  = 4 + 14 * 2^64
```

**Verification using highdigits/lowdigits:**

```
lowdigits (a+b) 1 = (a+b) % 2^64
                  = ((2^64-1 + 10*2^64) + (5 + 3*2^64)) % 2^64
                  = (13*2^64 + 4) % 2^64
                  = 4                     ✓

highdigits (a+b) 1 = (a+b) / 2^64
                   = (13*2^64 + 4) / 2^64
                   = 13                   ✓ (carry occurred: 13 = 10+3)
```

---

## Summary: Why These Functions Are Fundamental

These three functions (`bigdigit`, `highdigits`, `lowdigits`) are
fundamental for reasoning about multi-precision arithmetic because
they allow:

1. **Extract individual words** (`bigdigit`) - Essential for
   accessing components of a bignum

2. **Decompose numbers into parts** (`highdigits`/`lowdigits`) -
   Fundamental for induction and recursive proofs

3. **Prove algebraic properties** (like `high_low_digits`) - Foundation
   for all theorems about operations

### Relationship with Memory (s2n-bignum)

In s2n-bignum, a bignum of `k` words stored at address `addr`
represents the value:

**IMPORTANT:** Addresses are in **bytes**. Each 64-bit word = 8 bytes!

```
Memory (addresses in BYTES):
┌───────────────┬───────────────┬───────────────┬───────────────┐
│  word[0]      │  word[1]      │  word[2]      │  word[3]      │
│  64 bits      │  64 bits      │  64 bits      │  64 bits      │
│  (8 bytes)    │  (8 bytes)    │  (8 bytes)    │  (8 bytes)    │
│  addr+0       │  addr+8       │  addr+16      │  addr+24      │
└───────────────┴───────────────┴───────────────┴───────────────┘

Represented value:
  word[0] * 2^0  +
  word[1] * 2^64 +
  word[2] * 2^128 +
  word[3] * 2^192
```

Where `word[i] = bigdigit n i` - each word in memory corresponds
exactly to a `bigdigit`!

**Note on endianness:**
- **Little-endian at word level:** word[0] comes before word[1]
  in memory (least significant bits first)
- **Little-endian within each word:** on x86/ARM architectures, bytes
  within each 64-bit word are also little-endian
  (least significant byte at lower address)
