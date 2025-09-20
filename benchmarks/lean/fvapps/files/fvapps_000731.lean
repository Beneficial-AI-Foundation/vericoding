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
-- </vc-theorems>