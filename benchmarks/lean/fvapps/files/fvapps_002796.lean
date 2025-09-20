-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def between (a b : Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem between_length_matches_inputs {a b : Int} (h : a ≤ b) :
  (between a b).length = b - a + 1 :=
  sorry

theorem between_sequential {a b : Int} (h : a ≤ b) :
  ∀ i h1 h2, ((between a b)[i+1]'h1 = (between a b)[i]'h2 + 1) :=
  sorry

theorem between_bounds {a b : Int} (h : a ≤ b) :
  (between a b).head? = some a ∧ 
  (between a b).getLast? = some b :=
  sorry

theorem between_all_integers {a b : Int} (h : a ≤ b) :
  ∀ x, x ∈ between a b → x = x :=
  sorry
-- </vc-theorems>