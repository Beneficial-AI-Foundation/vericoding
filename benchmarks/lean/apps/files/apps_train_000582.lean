-- <vc-preamble>
def count_valid_shifts (n : Nat) (nums : List Nat) : Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def verify_shift (arr : List Nat) (shift_pos : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds (n : Nat) (nums : List Nat)
  (h1 : 2 ≤ n) (h2 : n ≤ 20) (h3 : nums.length = n) :
  0 ≤ count_valid_shifts n nums ∧ count_valid_shifts n nums ≤ n :=
sorry

theorem all_same_gives_zero (n : Nat)
  (h1 : 2 ≤ n) (h2 : n ≤ 20) :
  count_valid_shifts n (List.replicate n 1) = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_valid_shifts 6 [1, 1, 2, 1, 1, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_valid_shifts 6 [1, 1, 2, 1, 1, 2]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_valid_shifts 4 [1, 2, 1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible