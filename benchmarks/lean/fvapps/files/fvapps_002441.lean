-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def product (fracs: List (Int × Nat)): Int × Nat := sorry

theorem product_matches_fraction_multiplication 
  (fracs: List (Int × Nat)) (h: fracs.length > 0):
  ∃ (x: Int × Nat), product fracs = x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem product_result_is_simplified 
  (fracs : List (Int × Nat)) (h: fracs.length > 0):
  let res := product fracs
  ∃ g : Nat, g > 0 ∧ Nat.gcd res.1.natAbs res.2 = g := sorry 

theorem single_fraction_unchanged
  (n: Int) (d: Nat) (h: d > 0):
  product [(n,d)] = (n,d) := sorry

theorem empty_list_error
  (h: ¬∃ (x: Int × Nat), product [] = x):
  True := sorry
-- </vc-theorems>