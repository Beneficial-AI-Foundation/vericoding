-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numFactoredBinaryTrees (arr : Array Nat) : Nat := sorry

theorem numFactoredBinaryTrees_single_element
  (n : Nat)
  (h : n = 2) :
  numFactoredBinaryTrees #[n] = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numFactoredBinaryTrees_prime_numbers :
  numFactoredBinaryTrees #[2, 3, 5, 7] = 4 := sorry

theorem numFactoredBinaryTrees_perfect_squares :
  numFactoredBinaryTrees #[2, 4] > 2 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval numFactoredBinaryTrees #[2, 4]

/-
info: 7
-/
-- #guard_msgs in
-- #eval numFactoredBinaryTrees #[2, 4, 5, 10]

/-
info: 2
-/
-- #guard_msgs in
-- #eval numFactoredBinaryTrees #[2, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible