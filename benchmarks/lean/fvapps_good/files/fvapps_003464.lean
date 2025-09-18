-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def square (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_positive_integers (n : Int) (h : n ≥ 1) (h2 : n ≤ 20) : 
  square n = (2 : Int) * square (n-1) ∧ square n > 0 :=
  sorry

theorem square_invalid_inputs (n : Int) (h : n ≤ 0) :
  ¬∃ (result : Int), square n = result :=
  sorry
-- </vc-theorems>