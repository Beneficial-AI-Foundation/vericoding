/-
# Task
Your task is to find the sum for the range `0 ... m` for all powers from `0 ... n.

# Example

 For `m = 2, n = 3`, the result should be `20`

 `0^0+1^0+2^0 + 0^1+1^1+2^1 + 0^2+1^2+2^2 + 0^3+1^3+2^3 = 20`

 Note, that no output ever exceeds 2e9.

# Input/Output

 - `[input]` integer m

  `0 <= m <= 50000`

 - `[input]` integer `n`

  `0 <= n <= 9`

 - `[output]` an integer(double in C#)

  The sum value.
-/

-- <vc-helpers>
-- </vc-helpers>

def S2N (m n : Nat) : Nat := sorry

theorem s2n_nonnegative (m n : Nat) : 
  m ≤ 20 → n ≤ 10 → S2N m n ≥ 0 := sorry

theorem s2n_increasing_n (m n : Nat) :
  m ≤ 10 → n ≤ 5 → n > 0 → S2N m n ≥ S2N m (n-1) := sorry

theorem s2n_increasing_m (m n : Nat) :
  m ≤ 10 → n ≤ 5 → m > 0 → S2N m n ≥ S2N (m-1) n := sorry

theorem s2n_base_cases :
  (S2N 0 0 = 1) ∧ (S2N 1 0 = 2) ∧ (S2N 0 1 = 1) := sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval S2N 2 3

/-
info: 434
-/
-- #guard_msgs in
-- #eval S2N 3 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval S2N 1 1

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible