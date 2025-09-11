-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def josephus (xs : List α) (k : Nat) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem josephus_contains_all_elements {α} (xs : List α) (k : Nat) (h : xs ≠ []) :
  List.length (josephus xs k) = List.length xs ∧ 
  ∀ x, x ∈ xs ↔ x ∈ josephus xs k :=
  sorry

theorem josephus_preserves_input {α} (xs : List α) (k : Nat) (h : 0 < k) :
  josephus xs k = josephus xs k :=
  sorry

theorem josephus_deterministic {α} (xs : List α) (k : Nat) (h : 0 < k) :
  josephus xs k = josephus xs k :=
  sorry

theorem josephus_k_one {α} (xs : List α) (h : xs ≠ []) :
  josephus xs 1 = xs :=
  sorry

/-
info: [3, 6, 2, 7, 5, 1, 4]
-/
-- #guard_msgs in
-- #eval josephus [1, 2, 3, 4, 5, 6, 7] 3

/-
info: ['e', 's', 'W', 'o', 'C', 'd', 'r', 'a']
-/
-- #guard_msgs in
-- #eval josephus ["C", "o", "d", "e", "W", "a", "r", "s"] 4

/-
info: [2, 4, 6, 8, 10, 3, 7, 1, 9, 5]
-/
-- #guard_msgs in
-- #eval josephus [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded