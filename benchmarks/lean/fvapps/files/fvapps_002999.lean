-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fit_in (a b m n : Nat) : Bool := sorry

theorem fit_in_symmetry {a b m n : Nat} : 
  fit_in a b m n = fit_in b a m n ∧ 
  fit_in a b m n = fit_in a b n m := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fit_in_identical_small_dimensions {a b : Nat} :
  let m := min a b - 1
  ¬fit_in a b m m := sorry

theorem fit_in_large_container {a b : Nat} (h : a ≤ 1000) (h2 : b ≤ 1000) :
  let large := 2 * max a b + 10
  fit_in a b large large := sorry

theorem fit_in_constraints {a b m n : Nat} :
  fit_in a b m n → 
  max a b ≤ min m n ∧ 
  a + b ≤ max m n := sorry
-- </vc-theorems>