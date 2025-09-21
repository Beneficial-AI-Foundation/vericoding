-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def InsertBeforeEach (s : Array String) (x : String) : Array String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem InsertBeforeEach_spec (s : Array String) (x : String) :
let v := InsertBeforeEach s x
v.size = 2 * s.size ∧
∀ i, 0 ≤ i ∧ i < s.size →
(v[2*i]! = x ∧ v[2*i + 1]! = s[i]!) :=
sorry
-- </vc-theorems>