-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def round1 (x : Float) : Float := sorry

def predict (candidates : List String) (polls : List (List Float × Float)) : List (String × Float) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem round1_multiple_of_point_one (x : Float) : 
  let r := round1 x
  Float.abs (r * 10 - Float.round (r * 10)) < 1e-10 := sorry

theorem round1_close_to_input (x : Float) :
  Float.abs (x - round1 x) ≤ 0.05 + 1e-10 := sorry

theorem predict_contains_all_candidates (candidates : List String) (polls : List (List Float × Float)) :
  List.length (predict candidates polls) = List.length candidates := sorry

theorem predict_in_bounds (candidates : List String) (polls : List (List Float × Float)) (p : String × Float) :
  p ∈ predict candidates polls → 0 ≤ p.2 ∧ p.2 ≤ 100 := sorry

theorem predict_sums_to_hundred (candidates : List String) (polls : List (List Float × Float)) :
  let predictions := predict candidates polls
  Float.abs (List.foldl (fun acc p => acc + p.2) 0 predictions - 100) < 0.2 := sorry

theorem predict_rounded (candidates : List String) (polls : List (List Float × Float)) (p : String × Float) :
  p ∈ predict candidates polls →
  Float.abs (p.2 * 10 - Float.round (p.2 * 10)) < 1e-10 := sorry

/-
info: expected
-/
-- #guard_msgs in
-- #eval predict ["A", "B", "C"] [[[20, 30, 50], 1.0], [[40, 40, 20], 0.5], [[50, 40, 10], 2.0]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval predict candidates [[[30, 30, 40], 1.0], [[20, 40, 40], 1.0]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval predict candidates [[[45, 35, 20], 1.0]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded