-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry

def find_next_square (n : Nat) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_square_of_perfect (n : Nat) (h : ∃ k, n = k * k) : 
  find_next_square n = ((sqrt n + 1) * (sqrt n + 1)) := sorry

theorem non_square_returns_minus_one (n : Nat) (h : ¬∃ k, n = k * k) :
  find_next_square n = -1 := sorry
-- </vc-theorems>