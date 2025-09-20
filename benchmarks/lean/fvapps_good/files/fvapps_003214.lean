-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lowercase_count (s : String) : Nat := sorry

theorem lowercase_count_matches_filter (s : String) :
  lowercase_count s = (s.data.filter Char.isLower).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lowercase_count_non_negative (s : String) :
  lowercase_count s ≥ 0 := sorry

theorem all_lowercase_matches_length (s : String) :
  (s.data.all Char.isLower) → lowercase_count s = s.length := sorry
-- </vc-theorems>