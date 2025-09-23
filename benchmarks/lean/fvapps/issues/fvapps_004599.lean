-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_all_even_numbers (numbers: List Nat) (split_type: Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_all_even_numbers_preserves_sum 
  (numbers: List Nat) (split_type: Nat) (h: split_type ≤ 3) :
  List.sum numbers = List.sum (split_all_even_numbers numbers split_type) :=
  sorry

theorem split_all_even_numbers_positive
  (numbers: List Nat) (split_type: Nat) (h1: split_type ≤ 3) (h2: ∀ n ∈ numbers, n > 0) : 
  ∀ n ∈ (split_all_even_numbers numbers split_type), n > 0 :=
  sorry

theorem split_all_even_numbers_preserves_odd
  (numbers: List Nat) (split_type: Nat) (h: split_type ≤ 3) :
  ∀ n ∈ numbers, n % 2 = 1 → n ∈ (split_all_even_numbers numbers split_type) :=
  sorry

/-
info: [1, 5, 5, 1, 3]
-/
-- #guard_msgs in
-- #eval split_all_even_numbers [1, 10, 1, 3] 0

/-
info: [1, 1, 9, 1, 3]
-/
-- #guard_msgs in
-- #eval split_all_even_numbers test1 1

/-
info: [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]
-/
-- #guard_msgs in
-- #eval split_all_even_numbers test1 3

/-
info: [1, 1, 3, 3, 5]
-/
-- #guard_msgs in
-- #eval split_all_even_numbers [1, 1, 3, 8] 0

/-
info: [1, 1, 3, 1, 7]
-/
-- #guard_msgs in
-- #eval split_all_even_numbers test2 1

/-
info: [1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval split_all_even_numbers test2 2
-- </vc-theorems>