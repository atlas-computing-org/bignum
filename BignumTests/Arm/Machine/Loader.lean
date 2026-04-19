/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public meta import Bignum.Arm.Machine.Loader

open Bignum.Arm

/-!
## Tests for the ELF Loader utilities
-/

-- compareBytes: equal lists
#eval compareBytes [] []
-- Expected: ByteCompareResult.ok

#eval compareBytes [0x22, 0x00] [0x22, 0x00]
-- Expected: ByteCompareResult.ok

-- compareBytes: length mismatch
#eval compareBytes [0x22, 0x00] [0x22]
-- Expected: ByteCompareResult.lengthMismatch 2 1

-- compareBytes: byte mismatch at index 1
#eval compareBytes [0x22, 0x01] [0x22, 0x00]
-- Expected: ByteCompareResult.byteMismatch 1 0x01 0x00

-- formatBytesAsLeanDef
#eval formatBytesAsLeanDef "simple_mc" [0x22, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x01, 0xcb]

-- hexDump
#eval hexDump [0x21, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x00, 0x8b,
               0x43, 0x00, 0x80, 0xd2, 0x21, 0x7c, 0x03, 0x9b]
