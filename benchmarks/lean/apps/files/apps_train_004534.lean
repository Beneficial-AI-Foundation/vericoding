-- <vc-preamble>
def digitSum (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countComfortablePairs (l r : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem window_size (start : Nat) (window : Nat) 
  (h1 : start ≥ 1) (h2 : start ≤ 100) (h3 : window ≥ 0) (h4 : window ≤ 10) :
  let result := countComfortablePairs start (start + window)
  result ≥ 0 ∧ result ≤ (window + 1) * window / 2 :=
  sorry

theorem single_number (n : Nat) (h1 : n ≥ 1) (h2 : n ≤ 1000) :
  countComfortablePairs n n = 0 :=
  sorry

theorem pairs_symmetry (n : Nat) (h1 : n ≥ 1) (h2 : n ≤ 100) :
  let allPairs := countComfortablePairs 1 n
  allPairs ≥ 0 ∧ allPairs ≤ n * 2 :=
  sorry

theorem small_ranges :
  countComfortablePairs 1 1 = 0 ∧
  countComfortablePairs 1 2 ≥ 0 ∧
  countComfortablePairs 9 10 ≥ 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_comfortable_pairs 10 12

/-
info: 20
-/
-- #guard_msgs in
-- #eval count_comfortable_pairs 1 9

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_comfortable_pairs 13 13
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded