/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Machine.Decode

@[expose] public section

/-!
# ELF .text Section Loader

This module provides functionality to load machine code bytes from raw binary
files (extracted via `objcopy -j .text -O binary`) and verify them against
expected byte lists used in proofs.

## Design Rationale

Following the s2n-bignum approach (and June Lee's advice), we do NOT parse ELF
headers directly. Instead:

1. Use `objcopy -j .text -O binary input.o output.bin` to extract raw .text bytes
2. Read the raw binary file in Lean
3. Compare against the expected byte list in the proof source

The byte list in proof source is **human-readable redundancy** against unverified
loader bugs. The loader is OUTSIDE the trusted computing base -- it merely
provides a convenient way to extract and verify bytes, but the proof-level byte
list (e.g., `simple_mc` or `sequence_mc`) is the ground truth.

This corresponds to HOL Light's `define_assert_from_elf` which:
- Reads an ELF file
- Extracts the .text section
- Asserts that the bytes match a given list
- Defines the byte list as a constant

Source: s2n-bignum/common/elf.ml (HOL Light ELF loader -- not ported directly)

## Usage

### Step 1: Extract .text bytes from an object file

```bash
# Compile assembly to object file
as -o program.o program.s
# Extract raw .text bytes
objcopy -j .text -O binary program.o program.bin
```

### Step 2: Use in Lean

```lean
-- At elaboration time, read and display bytes from a file
#load_bytes "program.bin"

-- At runtime, verify bytes match expected
#eval assertBytesFromFile "program.bin" sequence_mc
```
-/

namespace Bignum.Arm

/-!
## Core IO Functions

These functions read raw binary files and convert them to `List UInt8`.
-/

/--
Read all bytes from a binary file, returning them as a `List UInt8`.

This is the fundamental building block for loading machine code from
files produced by `objcopy -j .text -O binary`.
-/
def readBinaryFile (path : System.FilePath) : IO (List UInt8) := do
  let bytes ← IO.FS.readBinFile path
  return bytes.toList

/--
Read all bytes from a binary file, returning them as a `ByteArray`.
-/
def readBinaryFileBytes (path : System.FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

/-!
## Byte Comparison

Functions for comparing expected byte lists against actual file contents.
These implement the verification step of `define_assert_from_elf`.
-/

/--
Result of comparing expected bytes against actual file bytes.
-/
inductive ByteCompareResult
  | ok : ByteCompareResult
  | lengthMismatch (expected actual : Nat) : ByteCompareResult
  | byteMismatch (index : Nat) (expected actual : UInt8) : ByteCompareResult
  deriving Repr

/--
Compare two byte lists element by element.

Returns `ok` if they match, or a description of the first mismatch.
-/
def compareBytes (expected actual : List UInt8) : ByteCompareResult :=
  if expected.length != actual.length then
    .lengthMismatch expected.length actual.length
  else
    let rec go (i : Nat) (es as_ : List UInt8) : ByteCompareResult :=
      match es, as_ with
      | [], [] => .ok
      | e :: es', a :: as_' =>
        if e == a then go (i + 1) es' as_'
        else .byteMismatch i e a
      | _, _ => .ok  -- unreachable given length check
    go 0 expected actual

def toHexStr (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  let digits := if digits.length < 2 then ['0'] ++ digits else digits
  String.ofList digits

/--
Pretty-print a ByteCompareResult for error messages.
-/
def ByteCompareResult.toString : ByteCompareResult → String
  | .ok => "OK: all bytes match"
  | .lengthMismatch exp act =>
    s!"Length mismatch: expected {exp} bytes, got {act} bytes"
  | .byteMismatch idx exp act =>
    s!"Byte mismatch at offset {idx}: expected 0x{toHexStr exp.toNat}, got 0x{toHexStr act.toNat}"

instance : ToString ByteCompareResult := ⟨ByteCompareResult.toString⟩

/--
Verify that a binary file contains exactly the expected bytes.

This is the core of `define_assert_from_elf`: it reads a file and checks
that its contents match the expected machine code byte list.

Returns `true` if bytes match, `false` otherwise. Prints diagnostics on mismatch.
-/
def assertBytesFromFile (path : System.FilePath) (expected : List UInt8) : IO Bool := do
  let actual ← readBinaryFile path
  match compareBytes expected actual with
  | .ok =>
    IO.println s!"[Loader] {path}: OK ({expected.length} bytes verified)"
    return true
  | result =>
    IO.println s!"[Loader] {path}: FAIL - {result}"
    return false

/-!
## Elaboration-Time Commands

These Lean commands allow reading byte files at elaboration time,
providing immediate feedback during development.
-/

open Lean Elab Command in
/--
`#load_bytes` command: read a binary file and display its bytes as a Lean list literal.

Usage:
```lean
#load_bytes "path/to/program.bin"
```

This outputs the bytes in a format suitable for copy-pasting into a
`def my_mc : List UInt8 := [...]` definition.
-/
elab "#load_bytes " path:str : command => do
  let pathStr := path.getString
  let bytes ← IO.FS.readBinFile pathStr
  let byteList := bytes.toList
  let toHex (n : Nat) : String :=
    let digits := Nat.toDigits 16 n
    let digits := if digits.length < 2 then ['0'] ++ digits else digits
    String.ofList digits
  let hexStrs := byteList.map fun b => s!"0x{toHex b.toNat}"
  -- Group by 4 for readability (one ARM instruction per line)
  let rec groupBy4 : List String → List (List String)
    | [] => []
    | a :: b :: c :: d :: rest => [a, b, c, d] :: groupBy4 rest
    | remaining => [remaining]
  let groups := groupBy4 hexStrs
  let lines := groups.map fun g => s!"   {", ".intercalate g},"
  let result := s!"[\n{"\n".intercalate lines}\n]"
  logInfo m!"Bytes from {pathStr} ({byteList.length} bytes):\n{result}"

/-!
## Formatting Utilities

Helpers for generating Lean source code from byte lists.
-/

/--
Format a byte list as a Lean definition string.

Given a name and byte list, produces output like:
```lean
def my_mc : List UInt8 :=
  [0x21, 0x00, 0x00, 0x8b,
   0x42, 0x00, 0x00, 0x8b]
```
-/
def formatBytesAsLeanDef (name : String) (bytes : List UInt8) : String :=
  let hexBytes := bytes.map fun b => s!"0x{toHexStr b.toNat}"
  -- Group into 4-byte chunks (one ARM instruction each)
  let rec group4 : List String → List (List String)
    | [] => []
    | a :: b :: c :: d :: rest => [a, b, c, d] :: group4 rest
    | remaining => [remaining]
  let groups := group4 hexBytes
  let lines := groups.map fun g => s!"   {", ".intercalate g}"
  s!"def {name} : List UInt8 :=\n  [{",\n".intercalate lines}]"

/--
Format a byte list as a hex dump string for debugging.

Example output:
```
00000000: 21 00 00 8b 42 00 00 8b  !...B...
00000008: 43 00 80 d2 21 7c 03 9b  C...!|..
```
-/
def hexDump (bytes : List UInt8) : String :=
  let chunks := chunkBy8 bytes
  let lines := chunks.zipIdx.map fun (chunk, i) =>
    let offset := i * 8
    let hexPart := " ".intercalate (chunk.map fun b => toHexStr b.toNat)
    let asciiPart := String.ofList (chunk.map fun b =>
      let n := b.toNat
      if 0x20 ≤ n && n < 0x7f then Char.ofNat n else '.')
    let offsetHex := Nat.toDigits 16 offset
    let offsetStr := String.ofList (List.replicate (8 - offsetHex.length) '0' ++ offsetHex)
    s!"{offsetStr}: {hexPart}  {asciiPart}"
  "\n".intercalate lines
where
  chunkBy8 : List UInt8 → List (List UInt8)
    | [] => []
    | a :: b :: c :: d :: e :: f :: g :: h :: rest =>
      [a, b, c, d, e, f, g, h] :: chunkBy8 rest
    | remaining => [remaining]

/-!
## Program Construction from Files

Convenience functions to create `Program` values from binary files.
-/

/--
Read a binary file and create a Program from its bytes.

This combines `readBinaryFile` with `Program.fromBytes`, providing
a single-step way to load a program from a file.

The file should contain raw .text bytes (produced by objcopy).
-/
def Program.fromFile (base_addr : Word64) (path : System.FilePath) : IO Program := do
  let bytes ← readBinaryFile path
  return Program.fromBytes base_addr bytes

/--
Read a binary file, verify against expected bytes, and create a Program.

This is the complete pipeline corresponding to `define_assert_from_elf`:
1. Read the file
2. Verify bytes match expected
3. Create the Program

Throws an error if bytes don't match.
-/
def Program.fromFileVerified (base_addr : Word64) (path : System.FilePath)
    (expected : List UInt8) : IO Program := do
  let actual ← readBinaryFile path
  match compareBytes expected actual with
  | .ok =>
    return Program.fromBytes base_addr expected
  | result =>
    throw (IO.userError s!"Byte verification failed for {path}: {result}")

/-!
## Demonstration with Sequence Example

The sequence tutorial defines `sequence_mc` with 16 bytes (4 instructions).
To verify these bytes against an object file:

```bash
# Create the assembly source
cat > /tmp/sequence.s << 'EOF'
.text
.global _start
_start:
    add x1, x1, x0
    add x2, x2, x0
    mov x3, #2
    mul x1, x1, x3
EOF

# Assemble (on macOS with Xcode)
as -o /tmp/sequence.o /tmp/sequence.s

# Extract raw .text bytes (use llvm-objcopy on macOS)
llvm-objcopy -j __text -O binary /tmp/sequence.o /tmp/sequence.bin
# Or on Linux:
# objcopy -j .text -O binary /tmp/sequence.o /tmp/sequence.bin

# Now in Lean, verify:
-- #load_bytes "/tmp/sequence.bin"
-- #eval assertBytesFromFile "/tmp/sequence.bin" sequence_mc
```
-/

/-!
## Tests

Unit tests for the byte comparison and formatting functions.
-/

-- Test: compareBytes on matching lists
#eval do
  let r := compareBytes [0x21, 0x00, 0x00, 0x8b] [0x21, 0x00, 0x00, 0x8b]
  return match r with | .ok => "PASS" | _ => "FAIL"

-- Test: compareBytes on mismatched lists
#eval do
  let r := compareBytes [0x21, 0x00, 0x00, 0x8b] [0x21, 0x00, 0xFF, 0x8b]
  return match r with | .byteMismatch 2 _ _ => "PASS" | _ => "FAIL"

-- Test: compareBytes on different lengths
#eval do
  let r := compareBytes [0x21, 0x00] [0x21, 0x00, 0x00]
  return match r with | .lengthMismatch 2 3 => "PASS" | _ => "FAIL"

-- Test: toHexStr
#eval toHexStr 0x8b   -- "8b"
#eval toHexStr 0x00   -- "00"
#eval toHexStr 0xff   -- "ff"

-- Test: formatBytesAsLeanDef
#eval formatBytesAsLeanDef "test_mc" [0x21, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x00, 0x8b]

-- Test: hexDump
#eval hexDump [0x21, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x00, 0x8b,
               0x43, 0x00, 0x80, 0xd2, 0x21, 0x7c, 0x03, 0x9b]

end Bignum.Arm
