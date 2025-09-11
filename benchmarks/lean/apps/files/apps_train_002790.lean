-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_cows (n: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_cows_positive_integers {n: Int} (h: 1 ≤ n ∧ n ≤ 20) : 
  count_cows n > 0 :=
  sorry

theorem count_cows_non_positive {n: Int} (h: n ≤ 0) :
  count_cows n = 1 :=
  sorry

theorem count_cows_sequence {n: Int} (h: n ≥ 3) :
  count_cows n = count_cows (n-1) + count_cows (n-3) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_cows 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_cows 3

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_cows 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded