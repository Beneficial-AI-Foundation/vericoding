-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueOccurrences (arr : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniqueOccurrences_returns_bool (arr : List Int) :
  uniqueOccurrences arr = true ∨ uniqueOccurrences arr = false := by
  sorry

theorem uniqueOccurrences_empty_array :
  uniqueOccurrences [] = true := by
  sorry

theorem uniqueOccurrences_single_element (x : Int) :
  uniqueOccurrences [x] = true := by
  sorry

theorem uniqueOccurrences_reverse (arr : List Int) :
  uniqueOccurrences arr = uniqueOccurrences arr.reverse := by
  sorry

theorem uniqueOccurrences_double (arr : List Int) :
  uniqueOccurrences arr = uniqueOccurrences (arr ++ arr) := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval unique_occurrences [1, 2, 2, 1, 1, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval unique_occurrences [1, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval unique_occurrences [-3, 0, 1, -3, 1, 1, 1, -3, 10, 0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded