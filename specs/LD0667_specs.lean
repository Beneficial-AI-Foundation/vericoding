-- <vc-preamble>
def IsDigit (c : Char) : Bool :=
48 ≤ c.toNat ∧ c.toNat ≤ 57
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsInteger (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsInteger_spec (s : String) :
IsInteger s ↔ (s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → IsDigit (s.get ⟨i⟩)) :=
sorry
-- </vc-theorems>