/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public meta import Bignum.Arm.Machine.Decode

open Bignum.Arm

/-!
## Tests for ARM Instruction Decoding
-/

-- Test 1: Decode ADD X2, X1, X0 = 0x8b000022
-- #eval decode 0x8b000022

-- Test 2: Decode SUB X2, X2, X1 = 0xcb010042
-- #eval decode 0xcb010042

-- Test 3: Invalid encoding → none
-- #eval decode 0x00000000

-- Test 4: Invalid encoding → none
-- #eval decode 0xffffffff

-- Test 5: Endianness — bytes [0x22, 0x00, 0x00, 0x8b] → 0x8b000022 = 2332033058
#eval ((0x22 : UInt32) ||| ((0x00 : UInt32) <<< 8) |||
       ((0x00 : UInt32) <<< 16) ||| ((0x8b : UInt32) <<< 24))

-- Test 6: Byte list decoding (Simple.lean program)
-- #eval decodeBytes [0x22, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x01, 0xcb]

-- Test 7: Program creation from bytes
-- #eval Program.fromBytes (BitVec.ofNat 64 0) [0x22, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x01, 0xcb]

-- Test 8: Bit extraction from 0x8b000022 (ADD X2, X1, X0)
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
