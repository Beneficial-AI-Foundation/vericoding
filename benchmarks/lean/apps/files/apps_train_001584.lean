-- <vc-preamble>
def multiply (n k: Nat) : Nat := sorry

theorem multiply_positive (n k: Nat) 
  (h1: n > 0) (h2: k > 0) : multiply n k > 0 :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n: Nat) : Bool := sorry

theorem multiply_one (k: Nat)
  (h: k > 0) : multiply 1 k = 1 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_k1_is_one (n: Nat)
  (h: n > 0) : multiply n 1 = 1 :=
sorry

theorem multiply_monotone_k (n k: Nat)
  (h1: n > 0) (h2: k > 1) : 
  multiply n k ≥ multiply n (k-1) :=
sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval multiply 24 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval multiply 100 1

/-
info: 18
-/
-- #guard_msgs in
-- #eval multiply 20 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible