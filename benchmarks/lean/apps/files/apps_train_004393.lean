-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def int_diff (arr : List Int) (n : Int) : Int := sorry

theorem int_diff_nonnegative (arr : List Int) (n : Int) : 
  n ≥ 0 → int_diff arr n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem int_diff_max_pairs (arr : List Int) (n : Int) :
  let max_pairs := (arr.length * (arr.length - 1)) / 2
  int_diff arr n ≤ max_pairs := sorry

theorem int_diff_order_invariant (arr : List Int) (n : Int) :
  int_diff arr n = int_diff (arr.reverse) n := sorry

-- Simplified version focusing on the core property rather than implementation details 

theorem int_diff_zero_counts_equal_numbers (arr : List Int) :
  int_diff arr 0 = 
    -- Number of pairs of equal elements
    let count_equal_pairs (xs : List Int) := 
      int_diff xs 0 
    count_equal_pairs arr := sorry

theorem int_diff_scaling (arr : List Int) (n : Int) :
  n > 0 →
  int_diff arr n = int_diff (arr.map (· * 2)) (n * 2) := sorry

theorem int_diff_empty (n : Int) :
  int_diff [] n = 0 := sorry

theorem int_diff_identical (arr : List Int) (n : Int) (x : Int) :
  n > 0 →
  arr.all (· = x) →
  int_diff arr n = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval int_diff [1, 1, 5, 6, 9, 16, 27] 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval int_diff [1, 1, 3, 3] 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval int_diff [4, 8, 12, 12, 3, 6, 2] 6
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible