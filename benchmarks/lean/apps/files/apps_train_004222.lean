-- <vc-preamble>
def sumin (n : Nat) : Nat := sorry
def sumax (n : Nat) : Nat := sorry

def sumsum (n : Nat) : Nat := sorry

def sumOfMins (n : Nat) : Nat := sorry

def sumOfMaxs (n : Nat) : Nat := sorry

theorem sumax_positive (n : Nat) (h : n > 0) :
  sumax n > 0 :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfSums (n : Nat) : Nat := sorry

theorem sumsum_equals_sumin_plus_sumax (n : Nat) :
  sumsum n = sumin n + sumax n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumin_positive (n : Nat) (h : n > 0) : 
  sumin n > 0 :=
sorry

theorem sumin_le_sumax (n : Nat) :
  sumin n ≤ sumax n :=
sorry

theorem sumax_ge_sumin (n : Nat) :
  sumax n ≥ sumin n :=
sorry

theorem sumsum_positive (n : Nat) (h : n > 0) :
  sumsum n > 0 :=
sorry

/-
info: 55
-/
-- #guard_msgs in
-- #eval sumin 5

/-
info: 91
-/
-- #guard_msgs in
-- #eval sumin 6

/-
info: 1240
-/
-- #guard_msgs in
-- #eval sumin 15

/-
info: 161
-/
-- #guard_msgs in
-- #eval sumax 6

/-
info: 61755
-/
-- #guard_msgs in
-- #eval sumax 45

/-
info: 671650
-/
-- #guard_msgs in
-- #eval sumax 100

/-
info: 252
-/
-- #guard_msgs in
-- #eval sumsum 6

/-
info: 93150
-/
-- #guard_msgs in
-- #eval sumsum 45

/-
info: 1010000
-/
-- #guard_msgs in
-- #eval sumsum 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible