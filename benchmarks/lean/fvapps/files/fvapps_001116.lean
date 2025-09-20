-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_imposter (n : Nat) (base : List Int) (game : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_imposter_correct (base : List Int) (imposter : Int) :
  imposter ∉ base →  -- assume imposter not in base list
  find_imposter (base.length) base (base ++ [imposter]) = imposter := by  
  sorry
-- </vc-theorems>