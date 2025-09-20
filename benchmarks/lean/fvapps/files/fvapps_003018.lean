-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_cents (s: String) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem test_whole_dollar_amounts (amount: String) (h: ∃ n: Nat, amount = s!"${n}.00") : 
  let n := Classical.choose h 
  to_cents amount = some (n * 100) := 
  sorry

theorem test_invalid_formats (amount: String) 
  (h: ¬∃ d₁ d₂: Nat, amount = s!"${d₁}.{d₂}" ∧ d₂ < 100) :
  to_cents amount = none :=
  sorry

theorem test_empty_string :
  to_cents "" = none :=
  sorry
-- </vc-theorems>