-- <vc-helpers>
-- </vc-helpers>

def solve_vasily_cards (n: Nat) (arr: List Nat) : Nat :=
  sorry

theorem vasily_cards_result_positive {n: Nat} {arr: List Nat}
  (h1: n ≥ 1)
  (h2: arr.length = n) 
  (h3: ∀ x ∈ arr, x ≥ 1) :
  solve_vasily_cards n arr > 0 := by
  sorry

theorem vasily_cards_result_bounded {n: Nat} {arr: List Nat}
  (h1: n ≥ 1)
  (h2: arr.length = n)
  (h3: ∃ m, ∀ x ∈ arr, x ≤ m) : 
  ∃ max_val, (∀ x ∈ arr, x ≤ max_val) ∧ solve_vasily_cards n arr ≤ n * max_val := by
  sorry

theorem vasily_cards_single_element {arr: List Nat}
  (h1: arr.length = 1) :
  solve_vasily_cards 1 arr = 1 := by
  sorry

theorem vasily_cards_identical_elements {n: Nat} {arr: List Nat} {v: Nat}
  (h1: n ≥ 1)
  (h2: arr.length = n)
  (h3: ∀ x ∈ arr, x = v) :
  solve_vasily_cards n arr = n := by
  sorry

theorem vasily_cards_single_large {n: Nat}
  (h1: n ≥ 1) :
  solve_vasily_cards 1 [n * 1000] = 1 := by
  sorry

theorem vasily_cards_all_same {n v: Nat}
  (h1: n ≥ 2)
  (h2: v ≥ 1) :
  solve_vasily_cards n (List.replicate n v) = n := by
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_vasily_cards 4 [6, 3, 1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_vasily_cards 1 [1000]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_vasily_cards 7 [3, 3, 3, 3, 3, 3, 3]

-- Apps difficulty: competition
-- Assurance level: unguarded