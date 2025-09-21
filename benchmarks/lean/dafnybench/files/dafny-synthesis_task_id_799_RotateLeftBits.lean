-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RotateLeftBits (n : UInt32) (d : Int) : UInt32 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RotateLeftBits_spec (n : UInt32) (d : Int) :
0 ≤ d ∧ d < 32 →
RotateLeftBits n d = ((UInt32.shiftLeft n (UInt32.ofNat d.toNat)) ||| (UInt32.shiftRight n (UInt32.ofNat (32 - d).toNat))) :=
sorry
-- </vc-theorems>