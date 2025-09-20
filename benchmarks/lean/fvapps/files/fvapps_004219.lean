-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GolfString := String

def golf_score_calculator (par: GolfString) (score: GolfString) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem golf_score_symmetric (par score: GolfString) : 
  golf_score_calculator par score = -(golf_score_calculator score par) :=
sorry

theorem golf_score_identity (score: GolfString) :
  golf_score_calculator score score = 0 := 
sorry

theorem golf_score_bounds (par score: GolfString) :
  let result := golf_score_calculator par score;
  let max_diff := 18 * 7;
  -max_diff ≤ result ∧ result ≤ max_diff :=
sorry
-- </vc-theorems>