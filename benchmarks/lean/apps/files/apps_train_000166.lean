-- <vc-helpers>
-- </vc-helpers>

def integerBreak (n : Nat) : Nat := sorry

theorem integerBreak_positive (n : Nat) (h : n ≥ 2) : 
  integerBreak n > 0 := sorry

theorem integerBreak_geq_n (n : Nat) (h : n ≥ 4) :
  integerBreak n ≥ n := sorry

theorem integerBreak_2 :
  integerBreak 2 = 1 := sorry 

theorem integerBreak_3 :
  integerBreak 3 = 2 := sorry

theorem integerBreak_better_than_naive_split (n : Nat) (h : n ≥ 4) :
  integerBreak n ≥ 2^(n/2) * (if n % 2 = 0 then 1 else n % 2) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval integer_break 2

/-
info: 36
-/
-- #guard_msgs in
-- #eval integer_break 10

/-
info: 18
-/
-- #guard_msgs in
-- #eval integer_break 8

-- Apps difficulty: interview
-- Assurance level: guarded