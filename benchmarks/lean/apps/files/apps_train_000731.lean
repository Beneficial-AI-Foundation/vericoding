-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.permutationInverse (xs: List Nat) : List Nat := sorry

def is_ambiguous_permutation (xs : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_property {xs : List Nat} :
  let result := is_ambiguous_permutation xs
  let inv := xs.permutationInverse
  let inv2 := inv.permutationInverse
  result → xs = inv2 := sorry

theorem permutation_symmetry {xs : List Nat} :
  let inv := xs.permutationInverse
  is_ambiguous_permutation xs = is_ambiguous_permutation inv := sorry

theorem identity_permutation {n : Nat} :
  let xs := List.range n
  is_ambiguous_permutation xs = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_ambiguous_permutation [1, 4, 3, 2]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_ambiguous_permutation [2, 3, 4, 5, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_ambiguous_permutation [1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded