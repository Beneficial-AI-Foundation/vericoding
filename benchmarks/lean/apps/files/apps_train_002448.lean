-- <vc-preamble>
def count_distinct_stamps (stamps : List String) : Nat := sorry

theorem count_distinct_stamps_bounded (stamps : List String) : 
  count_distinct_stamps stamps ≤ stamps.length := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_unique (l : List String) : Nat := sorry

theorem count_distinct_stamps_deterministic (stamps : List String) : 
  count_distinct_stamps stamps = count_distinct_stamps stamps := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_distinct_stamps_nonnegative (stamps : List String) :
  count_distinct_stamps stamps ≥ 0 := sorry 

theorem count_distinct_stamps_with_duplicates (stamps : List String) :
  count_distinct_stamps (stamps ++ stamps) = count_distinct_stamps stamps := sorry

theorem count_distinct_stamps_empty :
  count_distinct_stamps [] = 0 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_distinct_stamps ["UK", "China", "USA", "France", "New Zealand", "UK", "France"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_distinct_stamps ["India", "India", "India"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_distinct_stamps ["Japan", "Korea", "China"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible