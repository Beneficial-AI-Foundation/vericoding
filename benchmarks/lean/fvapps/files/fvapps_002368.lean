-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>