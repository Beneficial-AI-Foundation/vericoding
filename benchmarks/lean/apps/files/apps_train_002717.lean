def toDigits (n : Nat) : List Nat :=
  if n < 10 then [n]
  else (n % 10) :: toDigits (n / 10)

def sum_list : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + sum_list t

-- <vc-helpers>
-- </vc-helpers>

def power_sumDigTerm : Nat → Nat := sorry

-- Property that the sequence is strictly increasing

theorem power_sumDigTerm_increasing {n : Nat} : 
  n > 0 → power_sumDigTerm n < power_sumDigTerm (n + 1) := sorry

-- Property that each term is a perfect power with base equal to the sum of its digits

theorem power_sumDigTerm_perfect_power {n : Nat} (h : n > 0) :
  ∃ base power : Nat, 
    base ≥ 2 ∧ 
    power ≥ 2 ∧ 
    power_sumDigTerm n = base ^ power ∧
    base = sum_list (toDigits (power_sumDigTerm n)) := sorry

/-
info: 81
-/
-- #guard_msgs in
-- #eval power_sumDigTerm 1

/-
info: 512
-/
-- #guard_msgs in
-- #eval power_sumDigTerm 2

/-
info: 2401
-/
-- #guard_msgs in
-- #eval power_sumDigTerm 3

-- Apps difficulty: introductory
-- Assurance level: guarded