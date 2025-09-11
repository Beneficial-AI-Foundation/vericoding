-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (a b : String) : String := sorry

theorem solution_result_structure (a b : String) :
  (String.length a < String.length b → solution a b = a ++ b ++ a) ∧ 
  (String.length a ≥ String.length b → solution a b = b ++ a ++ b) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_result_length (a b : String) :
  String.length (solution a b) = 
    2 * min (String.length a) (String.length b) + 
    max (String.length a) (String.length b) := sorry

theorem solution_empty_string (s : String) :
  solution "" s = s ∧ solution s "" = s := sorry

/-
info: '1221'
-/
-- #guard_msgs in
-- #eval solution "1" "22"

/-
info: '1221'
-/
-- #guard_msgs in
-- #eval solution "22" "1"

/-
info: 'xyz'
-/
-- #guard_msgs in
-- #eval solution "" "xyz"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded