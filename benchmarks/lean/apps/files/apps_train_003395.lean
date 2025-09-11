-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def choose (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem choose_self (n : Nat) : choose n n = 1 :=
  sorry

theorem choose_zero (n : Nat) : choose n 0 = 1 :=
  sorry

theorem choose_symmetry {n k : Nat} (h : k ≤ n) : 
  choose n k = choose n (n - k) :=
  sorry

theorem choose_gt_n {n k : Nat} (h : n < k) : 
  choose n k = 0 :=
  sorry 

theorem choose_pos {n k : Nat} (h : k ≤ n) : 
  choose n k > 0 :=
  sorry

theorem pascal_triangle (n k : Nat) (h : 0 < k) (h2 : k ≤ n) :
  choose n k = choose (n-1) (k-1) + choose (n-1) k :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval choose 1 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval choose 5 4

/-
info: 252
-/
-- #guard_msgs in
-- #eval choose 10 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval choose 10 20

/-
info: 2598960
-/
-- #guard_msgs in
-- #eval choose 52 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible