/-
All of the animals are having a feast! Each animal is bringing one dish. There is just one rule: the dish must start and end with the same letters as the animal's name. For example, the great blue heron is bringing garlic naan and the chickadee is bringing chocolate cake.

Write a function `feast` that takes the animal's name and dish as arguments and returns true or false to indicate whether the beast is allowed to bring the dish to the feast.

Assume that `beast` and `dish` are always lowercase strings, and that each has at least two letters. `beast` and `dish` may contain hyphens and spaces, but these will not appear at the beginning or end of the string. They will not contain numerals.
-/

-- <vc-helpers>
-- </vc-helpers>

def feast (beast dish : String) : Bool :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded