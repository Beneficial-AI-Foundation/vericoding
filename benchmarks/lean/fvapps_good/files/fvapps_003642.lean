-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factors : Int → List Int 
  := sorry

variable (result : List Int)
-- </vc-definitions>

-- <vc-theorems>
theorem factors_positive_int (x : Int) (h : x > 0) : 
  let result := factors x
  (∀ f ∈ result, x % f = 0) ∧
  result.head? = some x ∧
  result.getLast? = some 1 :=
  sorry

theorem factors_non_positive (x : Int) (h : x ≤ 0) :
  factors x = [-1] :=
  sorry

theorem factors_float (x : Float) :
  factors 0 = [-1] :=
  sorry

theorem factors_invalid_type (x : String) :
  factors 0 = [-1] :=
  sorry
-- </vc-theorems>