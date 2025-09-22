-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tileRectangle (n m : Nat) : Nat := sorry

theorem square_input {n : Nat} (h : n > 0) : 
  tileRectangle n n = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiples {n : Nat} (h : n > 0) :
  tileRectangle n (2 * n) = 2 ∧ tileRectangle (2 * n) n = 2 := sorry

theorem lower_bound {n m : Nat} (hn : n > 0) (hm : m > 0) :
  tileRectangle n m ≥ 1 := sorry

theorem upper_bound {n m : Nat} (hn : n > 0) (hm : m > 0) :
  tileRectangle n m ≤ n * m := sorry
-- </vc-theorems>