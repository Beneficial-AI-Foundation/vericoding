-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mult_triangle (n : Nat) : Array Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mult_triangle_symmetry (n : Nat) (h : n ≥ 1) :
  let result := mult_triangle n
  result[0]! = (n * (n + 1) / 2) ^ 2
:= sorry

theorem mult_triangle_odd_formula (n : Nat) (h : n ≥ 1) (h₂ : n ≤ 10) :
  let result := mult_triangle n
  result[2]! = ((n + 1) / 2) ^ 4
:= sorry
-- </vc-theorems>