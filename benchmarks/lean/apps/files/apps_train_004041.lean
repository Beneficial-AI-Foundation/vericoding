-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def apparently (s : String) : String := sorry

def String.occurrences (needle haystack : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem and_but_count_preserved (s : String) :
  let result := apparently s
  (s.occurrences "and" = result.occurrences "and") ∧ 
  (s.occurrences "but" = result.occurrences "but") := sorry

theorem length_increases_by_apparently (s : String) :
  let result := apparently s
  let len_diff := result.length - s.length
  len_diff ≥ 0 ∧ len_diff % 11 = 0 := sorry

theorem empty_input_unchanged (s : String) :
  s = "" ∨ s = " " ∨ s = "  " →
  apparently s = s := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval apparently "It was great and I"ve never been on live television before but sometimes I don"t watch this."

/-
info: expected2
-/
-- #guard_msgs in
-- #eval apparently "but apparently"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval apparently "but and apparently apparently apparently apparently"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded