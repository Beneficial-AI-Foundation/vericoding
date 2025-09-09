-- <vc-helpers>
-- </vc-helpers>

def pythagoreanTriplet (n : Nat) : Option (Nat × Nat × Nat) :=
  sorry

-- For inputs n ≥ 60, if a triplet exists, it satisfies required properties

theorem triplet_properties {n : Nat} (h : n ≥ 60) 
    (res : pythagoreanTriplet n = some (a, b, c)) :
    0 < a ∧ a < b ∧ b < c ∧
    a * a + b * b = c * c ∧
    a * b * c = n :=
  sorry

-- No valid triplets exist for inputs < 60

theorem no_small_triplets {n : Nat} (h : n < 60) :
    pythagoreanTriplet n = none :=
  sorry

-- The smallest valid input (60) produces triplet (3,4,5)

theorem minimum_triplet :
    pythagoreanTriplet 60 = some (3, 4, 5) :=
  sorry

/-
info: [3, 4, 5]
-/
-- #guard_msgs in
-- #eval pythagorean_triplet 60

/-
info: [5, 12, 13]
-/
-- #guard_msgs in
-- #eval pythagorean_triplet 780

/-
info: [8, 15, 17]
-/
-- #guard_msgs in
-- #eval pythagorean_triplet 2040

-- Apps difficulty: introductory
-- Assurance level: unguarded