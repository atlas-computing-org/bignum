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
  -- MOVZ (Move wide with zero, 64-bit)
  -- Pattern: [sf=1; opc=10; 100101; hw:2; imm16:16; Rd:5]
  -- Bits 28-23 = 0b100101 identifies Move wide immediate family
  -- opc=10 (bits 30-29) selects MOVZ variant
  else if extractBits w 28 23 == 0b100101 then
    let sf := getBit w 31           -- 64-bit if 1
    let opc := extractBits w 30 29  -- 10 = MOVZ
    let hw := extractBits w 22 21   -- Shift: 00=0, 01=16, 10=32, 11=48
    let imm16 := extractBits w 20 5 -- 16-bit immediate
    let Rd := extractBits w 4 0     -- Destination register
    if sf && opc == 0b10 then
      let rd := decodeReg Rd
      let shift := hw.toNat * 16
      some (Instruction.MOVZ rd imm16.toNat shift)
    else
      none
  -- MUL (multiply, encoded as MADD with Ra=XZR)
  -- Pattern: [sf=1; op54=00; 11011; op31=000; Rm:5; o0=0; Ra=11111; Rn:5; Rd:5]
  -- Bits 28-24 = 0b11011 identifies Data Processing 3 source
  -- MADD: sf=1, op54=00, op31=000, o0=0
  -- MUL is MADD with Ra = 11111 (XZR)
  else if extractBits w 28 24 == 0b11011 then
    let sf := getBit w 31
    let op54 := extractBits w 30 29
    let op31 := extractBits w 23 21
    let Rm := extractBits w 20 16
    let o0 := getBit w 15
    let Ra := extractBits w 14 10
    let Rn := extractBits w 9 5
    let Rd := extractBits w 4 0
    -- Check: 64-bit, MADD (op54=00, op31=000, o0=0), Ra=11111 (MUL alias)
    if sf && op54 == 0 && op31 == 0 && !o0 && Ra == 0b11111 then
      let rd := decodeReg Rd
      let rn := decodeReg Rn
      let rm := decodeReg Rm
      some (Instruction.MUL rd rn rm)
    else
      none
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
  Program.fromBytes (BitVec.ofNat 64 pc) simple_program_bytes
```
-/
def Program.fromBytes (base_addr : Word64) (bytes : List UInt8) : Program :=
  { base_addr := base_addr
    instructions := decodeBytes bytes }

/-!
## Memory-Based Decoding

The `arm_decode` function reads an instruction from memory at a given PC.
This corresponds to HOL Light's fetch-decode-execute model where programs
live in memory.
-/

/--
Read 4 bytes from memory starting at the given address.
Returns `none` if any byte is uninitialized.
-/
def read4Bytes (s : ArmState) (addr : Word64) : Option (UInt8 × UInt8 × UInt8 × UInt8) :=
  match s.mem.read_byte addr,
        s.mem.read_byte (addr + 1),
        s.mem.read_byte (addr + 2),
        s.mem.read_byte (addr + 3) with
  | some b0, some b1, some b2, some b3 => some (b0, b1, b2, b3)
  | _, _, _, _ => none

/--
Decode an instruction from memory at the given PC.

This corresponds to HOL Light's `arm_decode` function which fetches and decodes
an instruction from the machine state's memory.

The function:
1. Reads 4 bytes from memory at the PC (little-endian)
2. Combines them into a 32-bit instruction word
3. Decodes the word into an `Instruction`

Returns `none` if:
- Any of the 4 bytes at PC are uninitialized
- The instruction encoding is invalid or unsupported
-/
def arm_decode (s : ArmState) (pc : Word64) : Option Instruction :=
  match read4Bytes s pc with
  | some (b0, b1, b2, b3) =>
    -- ARM is little-endian: byte 0 = bits 7-0, byte 3 = bits 31-24
    let word := b0.toUInt32
              ||| (b1.toUInt32 <<< 8)
              ||| (b2.toUInt32 <<< 16)
              ||| (b3.toUInt32 <<< 24)
    decode word
  | none => none

/--
Core decode lemma: given the four concrete byte values at `pc`..`pc+3`, resolve
`arm_decode` by computation.

This is the building block for `EXEC_N` theorems: callers extract the byte
values from `aligned_bytes_loaded` and delegate the actual decode to this lemma.
Analogous to what `ARM_MK_EXEC_RULE` does in HOL Light.
-/
theorem arm_decode_of_mem_bytes (s : ArmState) (pc : Word64)
    (b0 b1 b2 b3 : UInt8)
    (h0 : s.mem.read_byte pc = some b0)
    (h1 : s.mem.read_byte (pc + 1) = some b1)
    (h2 : s.mem.read_byte (pc + 2) = some b2)
    (h3 : s.mem.read_byte (pc + 3) = some b3)
    (instr : Instruction)
    (hdecode : decode (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
                       (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)) = some instr) :
    arm_decode s pc = some instr := by
  unfold arm_decode read4Bytes
  simp only [h0, h1, h2, h3, hdecode]

/--
`exec_at` is the Lean analogue of HOL Light's `ARM_MK_EXEC_RULE`.

Given `bytes_loaded` and a byte offset `i`, it resolves `arm_decode` at
`pc + BitVec.ofNat 64 i` purely by computation:
- byte extraction from `bytes_loaded` (by index)
- instruction decode via `decide` on concrete `UInt32`

In HOL Light, `ARM_MK_EXEC_RULE` generates one proved decode theorem per
instruction in a single pass. Here, `exec_at` is the reusable lemma that
each `EXEC_N` theorem delegates to, with `i` and `instr` instantiated
concretely, keeping `EXEC_N` proofs to two lines each.

Usage (see `Simple.lean`):
```lean
theorem EXEC_0 ... := by
  obtain ⟨_, hb⟩ := h
  have key := exec_at s pc simple_mc 0 hb (by decide)
                (Instruction.ADD Reg.X2 Reg.X1 Reg.X0) (by decide)
  rwa [show pc + BitVec.ofNat 64 0 = pc from by bv_omega] at key
```
-/
theorem exec_at (s : ArmState) (pc : Word64) (bytes : List UInt8) (i : Nat)
    (h : bytes_loaded s.mem pc bytes) (hi : i + 3 < bytes.length)
    (instr : Instruction)
    (hdecode : decode ((bytes[i]'(by omega)).toUInt32
                       ||| ((bytes[i + 1]'(by omega)).toUInt32 <<< 8)
                       ||| ((bytes[i + 2]'(by omega)).toUInt32 <<< 16)
                       ||| ((bytes[i + 3]'(by omega)).toUInt32 <<< 24)) = some instr) :
    arm_decode s (pc + BitVec.ofNat 64 i) = some instr := by
  unfold arm_decode read4Bytes
  have hb0 := h i     (by omega)
  have hb1 := h (i+1) (by omega)
  have hb2 := h (i+2) (by omega)
  have hb3 := h (i+3) (by omega)
  rw [show pc + BitVec.ofNat 64 i + 1 = pc + BitVec.ofNat 64 (i+1) from by bv_omega]
  rw [show pc + BitVec.ofNat 64 i + 2 = pc + BitVec.ofNat 64 (i+2) from by bv_omega]
  rw [show pc + BitVec.ofNat 64 i + 3 = pc + BitVec.ofNat 64 (i+3) from by bv_omega]
  simp only [hb0, hb1, hb2, hb3, hdecode]


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
