/-
# Pythagorean Triples

A Pythagorean triplet is a set of three numbers a, b, and c where `a^2 + b^2 = c^2`. In this Kata, you will be tasked with finding the Pythagorean triplets whose product is equal to `n`, the given argument to the function `pythagorean_triplet`.

## Your task

In this Kata, you will be tasked with finding the Pythagorean triplets whose product is equal to `n`, the given argument to the function, where `0 < n < 10000000`

## Examples

One such triple is `3, 4, 5`. For this challenge, you would be given the value `60` as the argument to your function, and then it would return the Pythagorean triplet in an array `[3, 4, 5]` which is returned in increasing order. `3^2 + 4^2 = 5^2` since `9 + 16 = 25` and then their product (`3 * 4 * 5`) is `60`.

More examples:

| **argument** | **returns** |
| ---------|---------|
| 60       | [3, 4, 5] |
| 780      | [5, 12, 13] |
| 2040     | [8, 15, 17] |
-/

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