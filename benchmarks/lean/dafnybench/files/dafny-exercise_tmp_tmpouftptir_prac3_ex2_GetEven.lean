-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GetEven (s : Array Nat) : Array Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem GetEven_spec (s : Array Nat) :
∀ i, 0 ≤ i ∧ i < s.size →
let s' := GetEven s
if s[i]! % 2 = 1
then s'[i]! = s[i]! + 1
else s'[i]! = s[i]! :=
sorry
-- </vc-theorems>