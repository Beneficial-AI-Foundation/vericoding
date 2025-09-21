-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SplitStringIntoChars (s : String) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SplitStringIntoChars_spec (s : String) :
let v := SplitStringIntoChars s
v.size = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length → v[i]! = s.get ⟨i⟩ :=
sorry
-- </vc-theorems>