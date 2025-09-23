-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unhappyFriends (n: Nat) (preferences: List (List Nat)) (pairs: List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unhappyFriends_output_is_nat (n: Nat) (preferences: List (List Nat)) (pairs: List (List Nat)) :
  n % 2 = 0 →
  n ≥ 2 → 
  n ≤ 6 →
  (∀ p ∈ preferences, p.length = n - 1) →
  (∀ p ∈ preferences, ∀ i, i ∈ p → i < n ∧ i ≠ preferences.indexOf p) →
  (∀ p ∈ pairs, p.length = 2) →
  (∀ p ∈ pairs, ∀ i ∈ p, i < n) →
  ∃ result, result = unhappyFriends n preferences pairs ∧ result ≤ n :=
sorry

theorem unhappyFriends_output_nonnegative (n: Nat) (preferences: List (List Nat)) (pairs: List (List Nat)) :
  n % 2 = 0 →
  n ≥ 2 →
  n ≤ 6 →
  (∀ p ∈ preferences, p.length = n - 1) →
  (∀ p ∈ preferences, ∀ i, i ∈ p → i < n ∧ i ≠ preferences.indexOf p) →
  (∀ p ∈ pairs, p.length = 2) →
  (∀ p ∈ pairs, ∀ i ∈ p, i < n) →
  unhappyFriends n preferences pairs ≥ 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval unhappyFriends 4 [[1, 2, 3], [3, 2, 0], [3, 1, 0], [1, 2, 0]] [[0, 1], [2, 3]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval unhappyFriends 2 [[1], [0]] [[1, 0]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval unhappyFriends 4 [[1, 3, 2], [2, 3, 0], [1, 3, 0], [0, 2, 1]] [[1, 3], [0, 2]]
-- </vc-theorems>