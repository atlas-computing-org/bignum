/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Machine.Decode

@[expose] public section

/-!
# Object File Loader

Loads ARM machine code bytes directly from object files (`.o`).

## Supported Formats

- **Mach-O 64-bit** (macOS ARM64): extracts `__TEXT,__text`
- **ELF 64-bit** (Linux AArch64): extracts `.text`

## Design Rationale

The byte list in a proof (e.g., `simple_mc`) is the **ground truth** of the
trusted computing base. The loader lives OUTSIDE the TCB — it provides a
convenient way to verify that the assembler produced the expected bytes.

This corresponds to HOL Light's `define_assert_from_elf`
(s2n-bignum/common/elf.ml), but parses object files directly in Lean.

## Usage

```lean
-- Show bytes from an object file at elaboration time
#load_obj "path/to/program.o"

-- Verify bytes at run time
#eval assertTextSectionFromObj "path/to/program.o" simple_mc

-- Load a Program directly
def p : IO Program := Program.fromObj 0 "path/to/program.o"
```
-/

namespace Bignum.Arm

/-!
## Binary Parsing Helpers

Little-endian field readers used by the Mach-O and ELF parsers. These are in the
public namespace to enable users to build additional parsers.
-/

def readLE16 (bytes : ByteArray) (off : Nat) : Option UInt16 :=
  if h : off + 2 ≤ bytes.size then
    some (bytes[off].toUInt16 ||| (bytes[off + 1].toUInt16 <<< 8))
  else none

def readLE32 (bytes : ByteArray) (off : Nat) : Option UInt32 :=
  if h : off + 4 ≤ bytes.size then
    let b (i : Nat) (hi : i < 4 := by omega) : UInt32 :=
      bytes[off + i].toUInt32
    some (b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24))
  else none

def readLE64 (bytes : ByteArray) (off : Nat) : Option UInt64 :=
  if h : off + 8 ≤ bytes.size then
    let b (i : Nat) (hi : i < 8 := by omega) : UInt64 :=
      bytes[off + i].toUInt64
    some (b 0         ||| (b 1 <<<  8) ||| (b 2 <<< 16) |||
         (b 3 <<< 24) ||| (b 4 <<< 32) ||| (b 5 <<< 40) |||
         (b 6 <<< 48) ||| (b 7 <<< 56))
  else none

/-- Read a null-terminated string from a fixed-width field (e.g., 16-byte
  sectname). -/
def readFixedStr (bytes : ByteArray) (off len : Nat) : String :=
  let raw := (List.range len).map fun i =>
    if off + i < bytes.size then bytes[off + i]! else 0
  String.ofList (raw.takeWhile (· != 0) |>.map (Char.ofNat ·.toNat))

/-- Extract a contiguous byte slice from a ByteArray. -/
def sliceBytes (bytes : ByteArray) (off size : Nat) : List UInt8 :=
  (List.range size).map fun i =>
    if off + i < bytes.size then bytes[off + i]! else 0

/-!
## Result Type
-/

/-- Result of extracting the text section from an object file. -/
inductive TextSectionResult
  | ok (bytes : List UInt8) : TextSectionResult
  | unknownFormat : TextSectionResult
  | sectionNotFound : TextSectionResult
  | parseError (msg : String) : TextSectionResult
  deriving Repr

instance : ToString TextSectionResult where
  toString
    | .ok bytes        => s!"OK: {bytes.length} bytes"
    | .unknownFormat   => "Unknown format (expected Mach-O 64 or ELF 64)"
    | .sectionNotFound => "Text section not found"
    | .parseError msg  => s!"Parse error: {msg}"

/-!
## Mach-O 64-bit Parser

Mach-O (macOS ARM64) binary layout:
```
Offset  Size  Field
0       4     magic = 0xFEEDFACF  (LE 64-bit Mach-O)
16      4     ncmds
32      ...   load commands
```

`LC_SEGMENT_64` (cmd = 0x19) — 72-byte header + N × 80-byte `section_64`:
```
segment_command_64 offsets:
  +8   segname (16)   +64  nsects (4)

section_64 offsets (each section, 80 bytes):
  +0   sectname (16)  +40  size (8)   ← byte count
  +48  offset (4)                     ← file offset of section data
```
-/
def parseMachO64 (bytes : ByteArray) : Option (List UInt8) :=
  if readLE32 bytes 0 != some 0xFEEDFACF then none
  else
    let ncmds := (readLE32 bytes 16).getD 0
    -- Walk load commands; carry (current_offset, found_result) as state. Note:
    -- in MH_OBJECT files the LC_SEGMENT_64 segname is "" (empty), not "__TEXT".
    -- We therefore check only sectname == "__text" inside every LC_SEGMENT_64.
    let (_, found) := (List.range ncmds.toNat).foldl (fun (lc_off, acc) _ =>
      match acc with
      | some _ => (lc_off, acc)   -- section found, skip remaining commands
      | none =>
        match readLE32 bytes lc_off, readLE32 bytes (lc_off + 4) with
        | some cmd, some cmdsize =>
          let result :=
            if cmd == 0x19 then  -- LC_SEGMENT_64 (any segment)
              let nsects := (readLE32 bytes (lc_off + 64)).getD 0
              -- Search sections for __text (each section_64 is 80 bytes)
              (List.range nsects.toNat).foldl (fun r i =>
                match r with
                | some _ => r
                | none =>
                  let soff := lc_off + 72 + i * 80
                  if readFixedStr bytes soff 16 == "__text" then
                    match readLE64 bytes (soff + 40), readLE32 bytes (soff + 48) with
                    | some sz, some fo => some (sliceBytes bytes fo.toNat sz.toNat)
                    | _, _             => none
                  else none) none
            else none
          (lc_off + cmdsize.toNat, result)
        | _, _ => (lc_off, none)) (32, none)
    found

/-!
## ELF 64-bit Parser

ELF 64-bit little-endian layout:
```
Offset  Size  Field
0       4     magic = 0x7f 'E' 'L' 'F'
4       1     class = 2 (64-bit)
5       1     data  = 1 (LE)
40      8     e_shoff     — section header table file offset
60      2     e_shnum     — number of section headers
62      2     e_shstrndx  — string table section index
```

Each section header (64 bytes):
```
+0   sh_name   (4)  — index into string table
+24  sh_offset (8)  ← file offset of section data
+32  sh_size   (8)  ← byte count of section data
```
-/
def parseELF64 (bytes : ByteArray) : Option (List UInt8) :=
  if bytes.size < 64
    || bytes[0]! != 0x7f || bytes[1]! != 0x45   -- 'E'
    || bytes[2]! != 0x4c || bytes[3]! != 0x46   -- 'L', 'F'
    || bytes[4]! != 2    || bytes[5]! != 1 then  -- 64-bit, LE
    none
  else do
    let shoff    ← readLE64 bytes 40
    let shnum    ← readLE16 bytes 60
    let shstrndx ← readLE16 bytes 62
    -- String table: section header at index shstrndx
    let strsh    := shoff.toNat + shstrndx.toNat * 64
    let strtab   ← readLE64 bytes (strsh + 24)   -- sh_offset of strtab section
    let strsz    ← readLE64 bytes (strsh + 32)   -- sh_size  of strtab section
    -- Scan section headers for ".text"
    (List.range shnum.toNat).foldl (fun acc i =>
      match acc with
      | some _ => acc
      | none =>
        let sh   := shoff.toNat + i * 64
        let ni   := (readLE32 bytes sh).getD 0
        if readFixedStr bytes (strtab.toNat + ni.toNat) strsz.toNat == ".text" then
          match readLE64 bytes (sh + 24), readLE64 bytes (sh + 32) with
          | some fo, some sz => some (sliceBytes bytes fo.toNat sz.toNat)
          | _, _             => none
        else none) none


/-!
## Public Extraction API
-/

/--
Extract the text section from a Mach-O or ELF 64-bit object file.
Automatically detects the format.
-/
def extractTextSection (bytes : ByteArray) : TextSectionResult :=
  if readLE32 bytes 0 == some 0xFEEDFACF then
    match parseMachO64 bytes with
    | some bs => .ok bs
    | none    => .sectionNotFound
  else if bytes.size ≥ 4
       && bytes[0]! == 0x7f && bytes[1]! == 0x45
       && bytes[2]! == 0x4c && bytes[3]! == 0x46 then
    match parseELF64 bytes with
    | some bs => .ok bs
    | none    => .sectionNotFound
  else
    .unknownFormat

/-- Read an object file and extract its text section. -/
def readTextSectionFromFile (path : System.FilePath) : IO TextSectionResult :=
  return extractTextSection (← IO.FS.readBinFile path)

/-!
## Byte Comparison
-/

def toHexStr (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (if digits.length < 2 then '0' :: digits else digits)

/-- Result of comparing two byte lists. -/
inductive ByteCompareResult
  | ok : ByteCompareResult
  | lengthMismatch (expected actual : Nat) : ByteCompareResult
  | byteMismatch (index : Nat) (expected actual : UInt8) : ByteCompareResult
  deriving Repr

def ByteCompareResult.toString : ByteCompareResult → String
  | .ok => "OK: all bytes match"
  | .lengthMismatch exp act =>
    s!"Length mismatch: expected {exp} bytes, got {act} bytes"
  | .byteMismatch idx exp act =>
    s!"Byte mismatch at offset {idx}: expected 0x{toHexStr exp.toNat}, got 0x{toHexStr act.toNat}"

instance : ToString ByteCompareResult := ⟨ByteCompareResult.toString⟩

/-- Compare two byte lists element by element. -/
def compareBytes (expected actual : List UInt8) : ByteCompareResult :=
  if expected.length != actual.length then
    .lengthMismatch expected.length actual.length
  else
    let rec go (i : Nat) : List UInt8 → List UInt8 → ByteCompareResult
      | [], []           => .ok
      | e :: es, a :: as_ =>
        if e == a then go (i + 1) es as_ else .byteMismatch i e a
      | _, _             => .ok  -- unreachable
    go 0 expected actual

/--
Verify that the text section of an object file matches expected bytes.

This is the Lean equivalent of `define_assert_from_elf`: reads the `.o`,
extracts the text section, and asserts it matches the proof-level byte list.
-/
def assertTextSectionFromObj (path : System.FilePath) (expected : List UInt8)
  : IO Bool := do
  match ← readTextSectionFromFile path with
  | .ok actual =>
    match compareBytes expected actual with
    | .ok =>
      IO.println s!"[Loader] {path}: OK ({expected.length} bytes verified)"
      return true
    | result =>
      IO.println s!"[Loader] {path}: FAIL - {result}"
      return false
  | e =>
    IO.println s!"[Loader] {path}: FAIL - {e}"
    return false

/-- Read a raw binary file (pre-extracted .text section). -/
def readBinaryFile (path : System.FilePath) : IO (List UInt8) :=
  return (← IO.FS.readBinFile path).toList

/--
Verify that a raw binary file matches expected bytes.
-/
def assertBytesFromFile (path : System.FilePath) (expected : List UInt8)
  : IO Bool := do
  let actual ← readBinaryFile path
  match compareBytes expected actual with
  | .ok =>
    IO.println s!"[Loader] {path}: OK ({expected.length} bytes verified)"
    return true
  | result =>
    IO.println s!"[Loader] {path}: FAIL - {result}"
    return false


/-!
## Program Construction
-/

/-- Load a Program directly from an object file (Mach-O or ELF). -/
def Program.fromObj (base_addr : Word64) (path : System.FilePath) : IO Program := do
  match ← readTextSectionFromFile path with
  | .ok bytes => return Program.fromBytes base_addr bytes
  | e => throw (IO.userError s!"Failed to load {path}: {e}")

/-- Load a Program from an object file and verify against expected bytes. -/
def Program.fromObjVerified (base_addr : Word64) (path : System.FilePath)
    (expected : List UInt8) : IO Program := do
  match ← readTextSectionFromFile path with
  | .ok actual =>
    match compareBytes expected actual with
    | .ok     => return Program.fromBytes base_addr expected
    | result  => throw (IO.userError s!"Byte mismatch in {path}: {result}")
  | e => throw (IO.userError s!"Failed to load {path}: {e}")

/-- Load a Program from a raw binary file (pre-extracted .text section). -/
def Program.fromFile (base_addr : Word64) (path : System.FilePath) : IO Program :=
  return Program.fromBytes base_addr (← readBinaryFile path)


/-!
## Formatting Utilities
-/

/-- Format a byte list as a Lean definition string. -/
def formatBytesAsLeanDef (name : String) (bytes : List UInt8) : String :=
  let hexBytes := bytes.map fun b => s!"0x{toHexStr b.toNat}"
  let rec group4 : List String → List (List String)
    | a :: b :: c :: d :: rest => [a, b, c, d] :: group4 rest
    | []       => []
    | remaining => [remaining]
  let groups := group4 hexBytes
  let firstLine := ", ".intercalate (groups.headD [])
  let restLines := groups.tail.map fun g => s!"   {", ".intercalate g}"
  s!"def {name} : List UInt8 :=\n  [{",\n".intercalate (firstLine :: restLines)}]"

/-- Format a byte list as a hex dump (8 bytes per line). -/
def hexDump (bytes : List UInt8) : String :=
  let chunks := chunkBy8 bytes
  let lines := chunks.zipIdx.map fun (chunk, i) =>
    let offset    := i * 8
    let hexPart   := " ".intercalate (chunk.map fun b => toHexStr b.toNat)
    let asciiPart := String.ofList (chunk.map fun b =>
      let n := b.toNat
      if 0x20 ≤ n && n < 0x7f then Char.ofNat n else '.')
    let offsetStr := String.ofList
      (List.replicate (8 - (Nat.toDigits 16 offset).length) '0' ++ Nat.toDigits 16 offset)
    s!"{offsetStr}: {hexPart}  {asciiPart}"
  "\n".intercalate lines
where
  chunkBy8 : List UInt8 → List (List UInt8)
    | a :: b :: c :: d :: e :: f :: g :: h :: rest =>
      [a, b, c, d, e, f, g, h] :: chunkBy8 rest
    | []       => []
    | remaining => [remaining]


/-!
## Elaboration-Time Commands

`elab` commands run in the Lean meta interpreter and cannot call `@[expose]`
(native) functions directly. Parsing is reimplemented inline using local lambdas.
-/

open Lean Elab Command in
/--
`#load_obj` — extract the `.text` section from an object file at elaboration time.

```lean
#load_obj "path/to/program.o"
```

Supports Mach-O (macOS `.o`) and ELF (Linux `.o`) object files.
Output is a Lean list literal suitable for use in a `def my_mc : List UInt8 := [...]`.
-/
elab "#load_obj " path:str : command => do
  let pathStr := path.getString
  let bytes ← IO.FS.readBinFile pathStr
  -- All helpers defined as local lambdas (pure, meta-compatible, capture bytes)
  let readLE32 : Nat → Option UInt32 := fun off =>
    if off + 4 ≤ bytes.size then
      let b := fun i => bytes[off + i]!.toUInt32
      some (b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24))
    else none
  let readLE64 : Nat → Option UInt64 := fun off =>
    if off + 8 ≤ bytes.size then
      let b := fun i => bytes[off + i]!.toUInt64
      some (b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24) |||
            (b 4 <<< 32) ||| (b 5 <<< 40) ||| (b 6 <<< 48) ||| (b 7 <<< 56))
    else none
  let readLE16 : Nat → Option UInt16 := fun off =>
    if off + 2 ≤ bytes.size then
      some (bytes[off]!.toUInt16 ||| (bytes[off + 1]!.toUInt16 <<< 8))
    else none
  let readStr : Nat → Nat → String := fun off len =>
    let raw := (List.range len).map fun i =>
      if off + i < bytes.size then bytes[off + i]! else 0
    String.ofList (raw.takeWhile (· != 0) |>.map (Char.ofNat ·.toNat))
  let slice : Nat → Nat → List UInt8 := fun off size =>
    (List.range size).map fun i =>
      if off + i < bytes.size then bytes[off + i]! else 0
  let result : Option (List UInt8) :=
    if readLE32 0 == some 0xFEEDFACF then
      -- Mach-O 64-bit
      let ncmds := (readLE32 16).getD 0
      let (_, found) := (List.range ncmds.toNat).foldl (fun (lc_off, acc) _ =>
        match acc with
        | some _ => (lc_off, acc)
        | none =>
          match readLE32 lc_off, readLE32 (lc_off + 4) with
          | some cmd, some cmdsize =>
            let r :=
              if cmd == 0x19 then  -- LC_SEGMENT_64 (segname may be "" in MH_OBJECT)
                let nsects := (readLE32 (lc_off + 64)).getD 0
                (List.range nsects.toNat).foldl (fun r i =>
                  match r with
                  | some _ => r
                  | none =>
                    let soff := lc_off + 72 + i * 80
                    if readStr soff 16 == "__text" then
                      match readLE64 (soff + 40), readLE32 (soff + 48) with
                      | some sz, some fo => some (slice fo.toNat sz.toNat)
                      | _, _             => none
                    else none) none
              else none
            (lc_off + cmdsize.toNat, r)
          | _, _ => (lc_off, none)) (32, none)
      found
    else if bytes.size ≥ 4
         && bytes[0]! == 0x7f && bytes[1]! == 0x45
         && bytes[2]! == 0x4c && bytes[3]! == 0x46
         && bytes[4]! == 2 && bytes[5]! == 1 then
      -- ELF 64-bit
      (do
        let shoff    ← readLE64 40
        let shnum    ← readLE16 60
        let shstrndx ← readLE16 62
        let strsh    := shoff.toNat + shstrndx.toNat * 64
        let strtab   ← readLE64 (strsh + 24)
        let strsz    ← readLE64 (strsh + 32)
        (List.range shnum.toNat).foldl (fun acc i =>
          match acc with
          | some _ => acc
          | none =>
            let sh := shoff.toNat + i * 64
            let ni := (readLE32 sh).getD 0
            if readStr (strtab.toNat + ni.toNat) strsz.toNat == ".text" then
              match readLE64 (sh + 24), readLE64 (sh + 32) with
              | some fo, some sz => some (slice fo.toNat sz.toNat)
              | _, _             => none
            else none) none)
    else none
  let toHex : Nat → String := fun n =>
    let d := Nat.toDigits 16 n
    String.ofList (if d.length < 2 then '0' :: d else d)
  match result with
  | none => logError m!"Could not extract text section from: {pathStr}"
  | some byteList =>
    let hexStrs := byteList.map fun b => s!"0x{toHex b.toNat}"
    let rec group4 : List String → List (List String)
      | a :: b :: c :: d :: rest => [a, b, c, d] :: group4 rest
      | []       => []
      | remaining => [remaining]
    let groups := group4 hexStrs
    let firstLine := ", ".intercalate (groups.headD [])
    let restLines := groups.tail.map fun g => s!"   {", ".intercalate g},"
    let body := "\n".intercalate restLines
    logInfo m!"-- {byteList.length} bytes from {pathStr}\n[\n  {firstLine},\n{body}\n]"

open Lean Elab Command in
/--
`#load_bytes` — display bytes from a raw binary file at elaboration time.

```lean
#load_bytes "path/to/program.bin"
```

For raw `.text` bytes pre-extracted via `objcopy -j .text -O binary`.
Prefer `#load_obj` for object files.
-/
elab "#load_bytes " path:str : command => do
  let pathStr := path.getString
  let byteList := (← IO.FS.readBinFile pathStr).toList
  let toHex : Nat → String := fun n =>
    let d := Nat.toDigits 16 n
    String.ofList (if d.length < 2 then '0' :: d else d)
  let hexStrs := byteList.map fun b => s!"0x{toHex b.toNat}"
  let rec group4 : List String → List (List String)
    | a :: b :: c :: d :: rest => [a, b, c, d] :: group4 rest
    | []       => []
    | remaining => [remaining]
  let groups := group4 hexStrs
  let firstLine := ", ".intercalate (groups.headD [])
  let restLines := groups.tail.map fun g => s!"   {", ".intercalate g},"
  let body := "\n".intercalate restLines
  logInfo m!"-- {byteList.length} bytes from {pathStr}\n[\n  {firstLine},\n{body}\n]"

end Bignum.Arm
