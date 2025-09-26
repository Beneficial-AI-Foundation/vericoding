import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers required
-- </vc-helpers>

-- <vc-definitions>
def RotateLeftBits (n : UInt32) (d : Int) : UInt32 :=
(UInt32.shiftLeft n (UInt32.ofNat d.toNat)) ||| (UInt32.shiftRight n (UInt32.ofNat (32 - d).toNat))
-- </vc-definitions>

-- <vc-theorems>
theorem RotateLeftBits_spec (n : UInt32) (d : Int) :
0 ≤ d ∧ d < 32 →
RotateLeftBits n d = ((UInt32.shiftLeft n (UInt32.ofNat d.toNat)) ||| (UInt32.shiftRight n (UInt32.ofNat (32 - d).toNat))) :=
by intros _; rfl
-- </vc-theorems>
