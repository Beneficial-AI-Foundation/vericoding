def check_perfect_number (n : Int) : Bool :=
  sorry

def perfect_numbers : List Int := [6, 28, 496, 8128, 33550336, 8589869056]

theorem known_perfect_numbers (n : Int) (h : n ∈ perfect_numbers) :
  check_perfect_number n = true :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def small_perfect_numbers : List Int := [6, 28, 496, 8128]

theorem most_numbers_not_perfect {n : Int} (h₁ : n ≥ 1) (h₂ : n ≤ 1000000)
  (h₃ : n ∉ small_perfect_numbers) :
  check_perfect_number n = false :=
  sorry

theorem non_positive_not_perfect {n : Int} (h : n ≤ 0) : 
  check_perfect_number n = false :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_perfect_number 28

/-
info: False
-/
-- #guard_msgs in
-- #eval check_perfect_number 12

/-
info: False
-/
-- #guard_msgs in
-- #eval check_perfect_number 1

-- Apps difficulty: introductory
-- Assurance level: unguarded