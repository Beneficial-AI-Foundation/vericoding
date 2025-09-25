-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ExtractRearChars (l : Array String) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ExtractRearChars_spec (l : Array String) :
(∀ i:Nat , 0 ≤ i ∧ i < l.size → (l[i]! |>.length) > 0) →
let r := ExtractRearChars l
(r.size = l.size) ∧
(∀ i:Nat , 0 ≤ i ∧ i < l.size →
r[i]! = (l[i]! |>.get ⟨((l[i]! |>.length) - 1)⟩)) :=
sorry
-- </vc-theorems>