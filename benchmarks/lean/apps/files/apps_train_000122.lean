-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search (list : List Int) (target : Int) : Bool := sorry

theorem search_target_in_list_returns_true (nums : List Int) (target : Int) : 
  search (nums ++ [target]) target = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem search_target_not_in_list_returns_false (nums : List Int) (target : Int) :
  (¬ target ∈ nums) → search nums target = false := sorry

theorem search_matches_contains (nums : List Int) (target : Int) :
  search nums target = (target ∈ nums) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval search [2, 5, 6, 0, 0, 1, 2] 0

/-
info: False
-/
-- #guard_msgs in
-- #eval search [2, 5, 6, 0, 0, 1, 2] 3

/-
info: True
-/
-- #guard_msgs in
-- #eval search [1] 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded