-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveMaxScore (n: Nat) (p: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solveMaxScore_nonnegative (n p : Nat) :
  n > 0 → p > 0 → solveMaxScore n p ≥ 0 := by
  sorry

theorem solveMaxScore_equal_inputs (n : Nat) :
  n > 0 → 
  let d := n % (n/2 + 1)
  if d = 0 then
    solveMaxScore n n = n * n * n 
  else 
    solveMaxScore n n = (n-d)*(n-d) + (n-d)*(n-n) + (n-n)*(n-n) := by
  sorry
-- </vc-theorems>