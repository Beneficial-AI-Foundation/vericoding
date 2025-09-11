-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def russian_peasant_multiplication (a : Int) (b : Nat) : Int := sorry

theorem russian_peasant_matches_multiplication {a : Int} {b : Nat} 
  (h1 : -10 ≤ a ∧ a ≤ 10) (h2 : b ≤ 10) :
  russian_peasant_multiplication a b = a * b := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem russian_peasant_multiply_zero_left :
  ∀ n : Nat, russian_peasant_multiplication 0 n = 0 := sorry

theorem russian_peasant_multiply_zero_right {n : Nat} :
  russian_peasant_multiplication n (Nat.zero) = 0 := sorry

theorem russian_peasant_small_nums_1 :
  russian_peasant_multiplication 2 3 = 6 := sorry

theorem russian_peasant_small_nums_2 :
  russian_peasant_multiplication 5 4 = 20 := sorry

/-
info: 50
-/
-- #guard_msgs in
-- #eval russian_peasant_multiplication 10 5

/-
info: 3150
-/
-- #guard_msgs in
-- #eval russian_peasant_multiplication 175 18
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible