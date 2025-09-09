def max_stones_removed (n : Nat) (piles : List Nat) : Nat := sorry

def list_sum : List Nat → Nat
  | [] => 0
  | x::xs => x + list_sum xs

-- <vc-helpers>
-- </vc-helpers>

def alternating_elements : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x::_::xs => x :: alternating_elements xs

theorem max_stones_removed_identity (n : Nat) (piles : List Nat) (h : piles.length > 0) :
  max_stones_removed n piles = max_stones_removed n piles := sorry

theorem max_stones_removed_n_independent (n₁ n₂ : Nat) (piles : List Nat) (h : piles.length > 0) :
  max_stones_removed n₁ piles = max_stones_removed n₂ piles := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_stones_removed 3 [1, 2, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_stones_removed 3 [1, 2, 1]

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_stones_removed 4 [4, 3, 2, 1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible