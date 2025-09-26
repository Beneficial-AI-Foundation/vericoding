-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_perfect_square (n : Nat) : Bool := sorry

theorem perfect_squares {n : Nat} : 
  is_perfect_square (n * n) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_perfect_squares {n : Nat} : 
  n > 0 → is_perfect_square (n * n + 1) = false := sorry

theorem sqrt_integers {n : Nat} :
  is_perfect_square n = 
  (∃ m : Nat, m * m = n) := sorry
-- </vc-theorems>