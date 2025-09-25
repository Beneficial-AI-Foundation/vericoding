-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ElementAtIndexAfterRotation (l : Array Int) (n : Nat) (index : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ElementAtIndexAfterRotation_spec
(l : Array Int) (n : Nat) (index : Nat) :
n ≥ 0 →
0 ≤ index →
index < l.size →
ElementAtIndexAfterRotation l n index = l[((index - n + l.size) % l.size)]! :=
sorry
-- </vc-theorems>