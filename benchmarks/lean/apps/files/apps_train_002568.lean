-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_score (xs : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_score_non_negative (xs : List Nat) 
  (h : ∀ x ∈ xs, x ≤ 4) : 
  0 ≤ get_score xs := sorry

theorem score_monotonic_increasing (arr : List Nat) 
  (h : ∀ x ∈ arr, x ≤ 4) (lines : Nat) (h2 : lines ≤ 4) :
  get_score arr ≤ get_score (arr ++ [lines]) := sorry

theorem level_multiplier_effect (arr : List Nat) 
  (h : arr ≠ []) (h2 : ∀ x ∈ arr, x ≤ 4) :
  let first := arr.head h
  get_score [first] ≤ get_score arr := sorry

theorem zero_lines_zero_score (arr : List Nat)
  (h : ∀ x ∈ arr, x = 0) :
  get_score arr = 0 := sorry

theorem score_deterministic (arr : List Nat)
  (h : ∀ x ∈ arr, x ≤ 4) :
  get_score arr = get_score arr := sorry

/-
info: 1640
-/
-- #guard_msgs in
-- #eval get_score [0, 1, 2, 3, 4]

/-
info: 620
-/
-- #guard_msgs in
-- #eval get_score [0, 1, 1, 3, 0, 2, 1, 2]

/-
info: 3300
-/
-- #guard_msgs in
-- #eval get_score [2, 0, 4, 2, 2, 3, 0, 0, 3, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded