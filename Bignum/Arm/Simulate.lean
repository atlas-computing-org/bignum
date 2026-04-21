/-
Copyright (c) 2025 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexandre Rademaker
-/
module

public import Bignum.Arm.Spec

@[expose] public section

/-!
# ARM Simulation

Executable simulation of ARM programs for development and debugging.

This module provides two complementary approaches to simulating ARM programs,
both usable with `#eval`. Unlike the formal proofs (which depend only on
`exec` and `step`), this module is **outside the TCB** — it is a development
tool, not part of the verification.

## Approach A — via `exec` (fast, uses pre-decoded instruction list)

```lean
#eval simulateExec simple_mc 0 [(Reg.X0, 5), (Reg.X1, 3)]
```

## Approach B — via fetch-decode-execute loop (faithful to hardware)

```lean
#eval simulateN 2 (mkInitState [(Reg.X0, 5), (Reg.X1, 3)]
                    |>.loadBytes 0 simple_mc
                    |>.setPC 0)
```

Both return the final `ArmState`, which can be inspected with `ArmState.showRegs`.
-/

namespace Bignum.Arm

/-!
## State Construction Helpers
-/

/--
Create an `ArmState` with all registers zero, all flags false, empty memory,
then initialize registers from the given list.
-/
def mkInitState (initRegs : List (Reg × UInt64)) : ArmState :=
  let s₀ : ArmState := {
    regs  := fun _ => 0,
    flags := { N := false, Z := false, C := false, V := false },
    mem   := Memory.empty
  }
  initRegs.foldl (fun s (r, v) => s.write_reg r (BitVec.ofNat 64 v.toNat)) s₀

/--
Load a byte list into an `ArmState`'s memory starting at `addr`.
-/
def ArmState.loadBytes (s : ArmState) (addr : Word64) (bytes : List UInt8) : ArmState :=
  { s with mem := s.mem.write_bytes addr bytes }

/--
Set the program counter.
-/
def ArmState.setPC (s : ArmState) (pc : UInt64) : ArmState :=
  s.write_reg Reg.PC (BitVec.ofNat 64 pc.toNat)

/-!
## Approach A: Simulation via `exec` (pre-decoded instruction list)

Uses `decodeBytes` to parse the bytes once, then runs `exec`.
-/

/--
**Approach A**: Simulate `mc` bytes starting at `base`, with given initial
register values. Decodes all bytes upfront via `decodeBytes`, then runs `exec`.

```lean
#eval simulateExec simple_mc 0 [(Reg.X0, 5), (Reg.X1, 3)]
```
-/
def simulateExec (mc : List UInt8) (base : UInt64)
    (initRegs : List (Reg × UInt64)) : ArmState :=
  let base_bv : Word64 := BitVec.ofNat 64 base.toNat
  let s₀ := (mkInitState initRegs).loadBytes base_bv mc |>.setPC base
  let instrs := decodeBytes mc
  exec instrs s₀

/-!
## Approach B: Simulation via fetch-decode-execute loop (faithful to hardware)

Uses `arm_decode` on the live memory state at each step, exactly as the `arm`
step relation does. Returns `none` if any decode fails.
-/

/--
**Approach B**: Execute exactly `n` fetch-decode-execute steps from state `s`.
Returns `none` if `arm_decode` fails at any point (invalid or missing bytes).

This matches the `arm` step relation precisely.
-/
def simulateN : Nat → ArmState → Option ArmState
  | 0,     s => some s
  | n + 1, s =>
    let pc := s.read_reg Reg.PC
    match arm_decode s pc with
    | none       => none
    | some instr => simulateN n (step instr s)

/--
Convenience wrapper: load `mc` bytes at `base`, set initial registers,
then execute `n` steps via the fetch-decode-execute loop.

```lean
#eval simulateLoop 2 simple_mc 0 [(Reg.X0, 5), (Reg.X1, 3)]
```
-/
def simulateLoop (n : Nat) (mc : List UInt8) (base : UInt64)
    (initRegs : List (Reg × UInt64)) : Option ArmState :=
  let base_bv : Word64 := BitVec.ofNat 64 base.toNat
  let s₀ := (mkInitState initRegs).loadBytes base_bv mc |>.setPC base
  simulateN n s₀

/-!
## Display Helpers
-/

/--
Show the values of all general-purpose registers and PC as a string list.
-/
def ArmState.showRegs (s : ArmState) : List String :=
  let gp : List String := (List.finRange 31).map fun i =>
    s!"X{i.val} = {s.read_reg (Reg.X i)}"
  let pc := s!"PC = {s.read_reg Reg.PC}"
  gp ++ [pc]

end Bignum.Arm
