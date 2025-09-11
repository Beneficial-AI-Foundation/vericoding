-- <vc-preamble>
def count_jewels (jewels stones : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseString (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_jewels_properties_non_negative (jewels stones : String) :
  count_jewels jewels stones ≥ 0 :=
  sorry

theorem count_jewels_bounded_by_stones (jewels stones : String) :
  count_jewels jewels stones ≤ stones.length :=
  sorry

theorem count_jewels_empty_jewels (stones : String) :
  count_jewels "" stones = 0 :=
  sorry

theorem count_jewels_empty_stones (jewels : String) :
  count_jewels jewels "" = 0 :=
  sorry

theorem count_jewels_duplicates (jewels stones : String) :
  count_jewels (jewels ++ jewels) stones = count_jewels jewels stones :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_jewels "abc" "abcdef"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_jewels "aA" "abAZ"

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_jewels "what" "none"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible