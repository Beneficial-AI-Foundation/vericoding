-- <vc-preamble>
def find_runner_up_score (scores: List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def all_lt (x : Int) (l : List Int) : Prop := 
  ∀ y, y ∈ l → y < x
-- </vc-definitions>

-- <vc-theorems>
theorem duplicate_max_case :
  find_runner_up_score [1, 2, 2] = 1 :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_runner_up_score [2, 3, 6, 6, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_runner_up_score [2, 2, 3, 4, 4]

/-
info: 50
-/
-- #guard_msgs in
-- #eval find_runner_up_score [-100, 0, 50, 100, 100]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible