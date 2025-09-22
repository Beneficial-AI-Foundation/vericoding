-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def int_rac (n : Nat) (guess : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem int_rac_perfect_squares_consistency (x : Nat)
  (h1 : x ≥ 1) (h2 : x ≤ 20) :
  let n := x * x
  let guess1 := max 1 (x - 1) 
  let guess2 := x + 1
  Nat.sub (int_rac n guess1) (int_rac n guess2) ≤ 1 ∧ 
  Nat.sub (int_rac n guess2) (int_rac n guess1) ≤ 1 := sorry
-- </vc-theorems>