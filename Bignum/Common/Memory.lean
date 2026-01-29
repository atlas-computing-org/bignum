/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module
public import Bignum.Common.Word
public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Memory Model

This file defines the memory model.

## Main Definitions

* `Address` - Memory addresses (64-bit)
* `Memory` - Memory state (functional map from addresses to bytes)
* `read_mem_bytes` - Read multiple bytes from memory
* `write_mem_bytes` - Write multiple bytes to memory
* `read_word64` - Read a 64-bit word from memory (little-endian)
* `write_word64` - Write a 64-bit word to memory (little-endian)

## References

This corresponds to the memory component in HOL Light's model.
Source: s2n-bignum/common/components.ml (memory-related definitions)
-/

namespace Bignum

/--
Memory addresses are 64-bit values.
-/
abbrev Address := Word64

/--
Memory is modeled as a partial function from addresses to bytes.
We use Option to represent potentially uninitialized memory.
-/
def Memory := Address → Option UInt8

/--
Empty memory (all addresses uninitialized).
-/
def Memory.empty : Memory := fun _ => none

/--
Read a single byte from memory at the given address.
-/
def Memory.read_byte (mem : Memory) (addr : Address)
  : Option UInt8 :=
  mem addr

/--
Write a single byte to memory at the given address.
-/
def Memory.write_byte (mem : Memory) (addr : Address) (byte : UInt8)
  : Memory :=
  fun a => if a = addr then some byte else mem a

/--
Read n bytes from memory starting at addr.
Returns None if any byte is uninitialized.
-/
def Memory.read_bytes (mem : Memory) (addr : Address) (n : Nat)
  : Option (List UInt8) :=
  let rec aux (i : Nat) (acc : List UInt8) : Option (List UInt8) :=
    if i = 0 then
      some acc.reverse
    else
      let offset := Word64.ofNat (n - i)
      match mem (addr + offset) with
      | none => none
      | some byte => aux (i - 1) (byte :: acc)
  aux n []

/--
Write bytes to memory starting at addr.
-/
def Memory.write_bytes (mem : Memory) (addr : Address) (bytes : List UInt8)
  : Memory :=
  bytes.zipIdx.foldl
    (fun m (byte, i) => m.write_byte (addr + Word64.ofNat i) byte)
    mem

/--
Read a 64-bit word from memory in little-endian format.
The address should be the lowest byte address.
-/
def Memory.read_word64 (mem : Memory) (addr : Address) : Option Word64 :=
  match mem.read_bytes addr 8 with
  | none => none
  | some bytes =>
    -- Combine 8 bytes in little-endian order
    -- byte[0] is least significant, byte[7] is most significant
    some <| bytes.zipIdx.foldl
      (fun acc (byte, i) => acc + Word64.ofNat (byte.toNat * 2^(8 * i)))
      0

/--
Write a 64-bit word to memory in little-endian format.
-/
def Memory.write_word64 (mem : Memory) (addr : Address) (w : Word64) : Memory :=
  let bytes := List.range 8 |>.map fun i =>
    UInt8.ofNat ((w.val / 2^(8 * i)) % 256)
  mem.write_bytes addr bytes

/--
Read a bignum (multiple 64-bit words) from memory.
The bignum is stored as an array of n words at address addr.

Corresponds to HOL Light's `bignum_from_memory`.
Source: s2n-bignum proofs use this extensively (e.g., bignum_add.ml:91-92)
-/
def Memory.read_bignum (mem : Memory) (addr : Address) (n : ℕ) : Option ℕ :=
  let rec aux (i : ℕ) (acc : ℕ) : Option ℕ :=
    if i = 0 then
      some acc
    else
      let word_addr := addr + Word64.ofNat (8 * (n - i))
      match mem.read_word64 word_addr with
      | none => none
      | some w => aux (i - 1) (acc + 2^(64 * (n - i)) * w.val)
  aux n 0

/--
Write a bignum to memory as n 64-bit words.
-/
def Memory.write_bignum (mem : Memory) (addr : Address) (n : ℕ) (val : ℕ) : Memory :=
  List.range n |>.foldl
    (fun m i =>
      let word_addr := addr + Word64.ofNat (8 * i)
      let word := Word64.ofNat ((val / 2^(64 * i)) % 2^64)
      m.write_word64 word_addr word)
    mem

/--
Check if two memory regions do not overlap. This corresponds to HOL Light's
`nonoverlapping`, used extensively in preconditions.

Source: s2n-bignum/common/overlap.ml
-/
def nonoverlapping
  (addr1 : Address) (size1 : ℕ) (addr2 : Address) (size2 : ℕ) : Prop :=
  addr1.val + size1 ≤ addr2.val ∨ addr2.val + size2 ≤ addr1.val

/--
Bytes are loaded and aligned at a given address. Corresponds to HOL Light's
`aligned_bytes_loaded`.
-/
def aligned_bytes_loaded (mem : Memory) (addr : Address) (bytes : List UInt8)
  : Prop :=
  addr.val % 4 = 0 ∧  -- 4-byte alignment
  ∀ i, (h : i < bytes.length) →
    mem.read_byte (addr + Word64.ofNat i) = some (bytes[i]'h)

end Bignum
