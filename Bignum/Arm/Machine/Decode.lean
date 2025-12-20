/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Machine.Instruction
public import Bignum.Arm.Machine.State

@[expose] public section

/-!
# ARM Instruction Decoding

Decodes 32-bit ARM AArch64 instruction encodings into the Instruction type.

This implements functionality similar to HOL Light's `decode` function and
`ARM_MK_EXEC_RULE`, allowing programs to be loaded from byte sequences as in
s2n-bignum.

## Main Definitions

* `extractBits` - Extract a bit field from a 32-bit word
* `getBit` - Extract a single bit
* `decodeReg` - Convert 5-bit register field to Reg type
* `decode` - Decode a 32-bit instruction encoding to Option Instruction
* `decodeBytes` - Decode a byte list (little-endian) into instruction list
* `Program.fromBytes` - Create a Program from byte sequence

## Known Encodings (from Simple.lean)

* `0x8b000022` = ADD X2, X1, X0
* `0xcb010042` = SUB X2, X2, X1

## References

Source: s2n-bignum/arm/proofs/decode.ml (HOL Light decode implementation)
Source: s2n-bignum/arm/tutorial/simple.ml:22-37 (byte list representation)

## Implementation Notes

This MVP implementation supports:
- ADD/SUB (register, no shift, 64-bit only)

Future extensions will add:
- ADDS/SUBS/ADCS/SBCS (variants with flags)
- Logical operations (AND/ORR/EOR)
- MOVZ/MOV
- LSL/LSR
- LDR/STR (memory operations)
- Branches (B/BL/Bcond/CBZ/CBNZ)
-/

namespace Bignum.Arm

/-!
## Bit Extraction Helpers

ARM instructions are 32-bit little-endian values. Bits are numbered from LSB
(bit 0) to MSB (bit 31).
-/

/--
Extract bits [high:low] (inclusive) from a 32-bit word.

Example: extractBits 0x8b000022 4 0 extracts bits 4-0, yielding 0x2 (register Rd).
-/
def extractBits (w : UInt32) (high low : Nat) : UInt32 :=
  ((w >>> low.toUInt32) &&& ((1 <<< (high - low + 1).toUInt32) - 1))

/--
Extract a single bit at position n.

Example: getBit 0x8b000022 31 extracts the sf bit (64-bit operation), yielding true.
-/
def getBit (w : UInt32) (n : Nat) : Bool :=
  ((w >>> n.toUInt32) &&& 1) != 0

/-!
## Register Decoding

ARM uses 5-bit register fields that can encode:
- 0-30: General purpose registers X0-X30
- 31: SP (stack pointer) or XZR (zero register), context-dependent

For the MVP, we treat register field 31 as SP uniformly.
-/

/--
Convert a 5-bit register field to Reg type.

Register encoding:
- 0-30 → X0-X30 (general purpose registers)
- 31 → SP (stack pointer)

Note: ARM uses register 31 as either SP or XZR (zero register) depending on
context. This MVP implementation always interprets it as SP.
-/
def decodeReg (bits : UInt32) : Reg :=
  let n := bits.toNat
  if h : n < 31 then
    Reg.X ⟨n, h⟩
  else
    Reg.SP

/-!
## Instruction Decoder

The decoder pattern-matches on instruction encoding bits following the ARM
Architecture Reference Manual (ARM ARM) specifications.

Each instruction type has a specific bit pattern:
```
ADD/SUB (register):
  31    30  29  28-24   23-22 21 20-16     15-10      9-5    4-0
  sf=1  op  S=0 01011   00    0  Rm=5bits  000000     Rn     Rd

  sf=1: 64-bit operation (we only support 64-bit)
  op=0: ADD, op=1: SUB
  S=0: Don't set flags (plain ADD/SUB, not ADDS/SUBS)
  shift=00, sam=000000: No shift applied
```

Source: ARM ARM section C3.5.1 (Data-processing - register)
HOL Light: s2n-bignum/arm/proofs/decode.ml:165-350
-/

/--
Decode a 32-bit ARM instruction encoding to an Instruction.

Returns `some instruction` for valid encodings, `none` for:
- Invalid/unrecognized instruction patterns
- Instructions not yet implemented in this MVP
- Instructions with unsupported operand combinations

Examples:
```lean
#eval decode 0x8b000022  -- some (ADD X2 X1 X0)
#eval decode 0xcb010042  -- some (SUB X2 X2 X1)
#eval decode 0x00000000  -- none (invalid)
```
-/
def decode (w : UInt32) : Option Instruction :=
  -- ADD/SUB (register, no shift, 64-bit)
  -- Pattern: [sf; op; S; 01011:5; 00:2; 0:1; Rm:5; 000000:6; Rn:5; Rd:5]
  -- Bits 28-21 = 0b01011000 identifies ADD/SUB register family
  if extractBits w 28 21 == 0b01011000 then
    let sf := getBit w 31        -- 64-bit if 1
    let op := getBit w 30        -- 0=ADD, 1=SUB
    let S := getBit w 29         -- Set flags (ADDS/SUBS)
    let Rm := extractBits w 20 16  -- Source register 2
    let sam := extractBits w 15 10 -- Shift amount (should be 0)
    let Rn := extractBits w 9 5    -- Source register 1
    let Rd := extractBits w 4 0    -- Destination register
    -- Check constraints: 64-bit, no flags, no shift
    if sf && !S && sam == 0 then
      let rd := decodeReg Rd
      let rn := decodeReg Rn
      let rm := decodeReg Rm
      -- Decide between SUB and ADD based on op bit
      if op then
        some (Instruction.SUB rd rn rm)
      else
        some (Instruction.ADD rd rn rm)
    else
      none  -- Unsupported: 32-bit, or with flags/shift
  else
    -- Other instruction families not yet implemented
    none

/-!
## Byte List Decoding

ARM instructions are stored in memory as 4-byte sequences in little-endian
format. The decodeBytes function converts a byte list into a list of
Instructions.

Little-endian layout:
```
Bytes: [0x22, 0x00, 0x00, 0x8b] → Word: 0x8b000022
       byte0  byte1  byte2  byte3        MSB ← LSB
```
-/

/--
Decode a list of bytes (little-endian) into a list of Instructions.

The function processes bytes 4 at a time, converting each 4-byte sequence
into a 32-bit word (little-endian), then decoding the instruction.

Stops at:
- End of byte list
- Invalid instruction (returns instructions decoded so far)
- Incomplete instruction (< 4 bytes remaining)

Example:
```lean
#eval decodeBytes [0x22, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x01, 0xcb]
-- Expected: [ADD X2 X1 X0, SUB X2 X2 X1]
```
-/
def decodeBytes (bytes : List UInt8) : List Instruction :=
  let rec go (bs : List UInt8) (acc : List Instruction) : List Instruction :=
    match bs with
    | b0 :: b1 :: b2 :: b3 :: rest =>
      -- ARM is little-endian: byte 0 = bits 7-0, byte 3 = bits 31-24
      let word := b0.toUInt32
                ||| (b1.toUInt32 <<< 8)
                ||| (b2.toUInt32 <<< 16)
                ||| (b3.toUInt32 <<< 24)
      match decode word with
      | some instr => go rest (acc ++ [instr])
      | none => acc  -- Stop on invalid instruction
    | _ => acc  -- Not enough bytes for a full instruction
  go bytes []

/--
Create a Program from a byte sequence.

This is the primary interface for loading programs from byte representations,
matching the HOL Light style used in s2n-bignum.

Example usage (from Simple.lean):
```lean
def simple_program_bytes : List UInt8 :=
  [0x22, 0x00, 0x00, 0x8b,  -- ADD X2, X1, X0
   0x42, 0x00, 0x01, 0xcb]  -- SUB X2, X2, X1

def simple_program (pc : Nat) : Program :=
  Program.fromBytes (Word64.ofNat pc) simple_program_bytes
```
-/
def Program.fromBytes (base_addr : Word64) (bytes : List UInt8) : Program :=
  { base_addr := base_addr
    instructions := decodeBytes bytes }

/-!
## Tests and Validation

These tests verify the decoder against known instruction encodings from the
Simple.lean tutorial.
-/

-- Test 1: Decode ADD X2, X1, X0
-- Binary: 10001011 00000000 00000000 00100010 = 0x8b000022
-- Expected: ADD X2, X1, X0
-- #eval decode 0x8b000022
-- Note: Commented out due to missing native implementation for Instruction repr

-- Test 2: Decode SUB X2, X2, X1
-- Binary: 11001011 00000001 00000000 01000010 = 0xcb010042
-- Expected: SUB X2, X2, X1
-- #eval decode 0xcb010042

-- Test 3: Invalid encoding (all zeros)
-- Expected: none
-- #eval decode 0x00000000

-- Test 4: Invalid encoding (all ones)
-- Expected: none
-- #eval decode 0xffffffff

-- Test 5: Endianness verification
-- Bytes [0x22, 0x00, 0x00, 0x8b] should form 0x8b000022
#eval ((0x22 : UInt32) ||| ((0x00 : UInt32) <<< 8) |||
       ((0x00 : UInt32) <<< 16) ||| ((0x8b : UInt32) <<< 24))
-- Expected: 0x8b000022 = 2332033058

-- Test 6: Byte list decoding (Simple.lean program)
-- Expected: Two instructions (ADD and SUB)
-- #eval decodeBytes [0x22, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x01, 0xcb]

-- Test 7: Program creation from bytes
-- #eval Program.fromBytes (Word64.ofNat 0)
--                         [0x22, 0x00, 0x00, 0x8b,
--                          0x42, 0x00, 0x01, 0xcb]

-- Test 8: Bit extraction helpers
#eval extractBits 0x8b000022 31 31  -- sf bit = 1
#eval extractBits 0x8b000022 30 30  -- op bit = 0
#eval extractBits 0x8b000022 29 29  -- S bit = 0
#eval extractBits 0x8b000022 28 21  -- opcode = 0b01011000 = 88
#eval extractBits 0x8b000022 4 0    -- Rd = 2

-- Test 9: Register decoding
-- #eval decodeReg 0   -- X0
-- #eval decodeReg 1   -- X1
-- #eval decodeReg 2   -- X2
-- #eval decodeReg 31  -- SP

/-!
## Helper Lemmas for Proofs

These lemmas help bridge the gap between decoded byte sequences and manually
constructed programs, making proofs more maintainable.
-/

/--
Program.fromBytes preserves the base address.
-/
theorem Program.fromBytes_base_addr (addr : Word64) (bytes : List UInt8) :
  (Program.fromBytes addr bytes).base_addr = addr := by
  unfold Program.fromBytes
  rfl

/--
Program.fromBytes decodes bytes into the instruction list.
-/
theorem Program.fromBytes_instructions (addr : Word64) (bytes : List UInt8) :
  (Program.fromBytes addr bytes).instructions = decodeBytes bytes := by
  unfold Program.fromBytes
  rfl

end Bignum.Arm
