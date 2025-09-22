-- <vc-preamble>
def all_lt (x : Int) (l : List Int) : Prop :=
  ∀ y, y ∈ l → y < x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_runner_up_score (scores: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem duplicate_max_case :
  find_runner_up_score [1, 2, 2] = 1 :=
sorry
-- </vc-theorems>