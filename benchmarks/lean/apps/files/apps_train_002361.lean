-- <vc-helpers>
-- </vc-helpers>

def add_digits (n : Nat) : Nat :=
  sorry

theorem add_digits_range (n : Nat) (h : n ≤ 10^6) :
  0 ≤ add_digits n ∧ add_digits n ≤ 9 :=
  sorry

partial def digit_sum (x : Nat) : Nat :=
  if x = 0 then 0
  else 
    let sum := digit_sum (x / 10) + x % 10
    if sum > 9 then digit_sum sum else sum

theorem add_digits_zero : 
  add_digits 0 = 0 :=
  sorry

theorem add_digits_nonzero (n : Nat) (h₁ : n ≤ 10^6) (h₂ : n > 0) :
  add_digits n > 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval add_digits 38

/-
info: 0
-/
-- #guard_msgs in
-- #eval add_digits 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval add_digits 789

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible