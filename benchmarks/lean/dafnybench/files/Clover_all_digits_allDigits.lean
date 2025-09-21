-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allDigits (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem allDigits_spec (s : String) :
allDigits s = true ↔ (∀ i, 0 ≤ i ∧ i < s.length → (s.get ⟨i⟩).isDigit) :=
sorry
-- </vc-theorems>