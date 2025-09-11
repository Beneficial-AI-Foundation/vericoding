-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def feast (beast dish : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem feast_properties (beast dish : String) 
  (h1 : beast.length > 0) (h2 : dish.length > 0) :
  feast beast dish = (beast.front == dish.front ∧ beast.back == dish.back) :=
sorry

theorem feast_same_string (s : String) (h : s.length > 0) :
  feast s s = true :=
sorry

theorem feast_first_last_only (beast dish : String)
  (h1 : beast.length > 1) (h2 : dish.length > 1) :
  let modifiedDish := String.mk [beast.front] ++ String.mk [beast.back]
  feast beast modifiedDish = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval feast "great blue heron" "garlic naan"

/-
info: True
-/
-- #guard_msgs in
-- #eval feast "chickadee" "chocolate cake"

/-
info: False
-/
-- #guard_msgs in
-- #eval feast "cat" "yogurt"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded