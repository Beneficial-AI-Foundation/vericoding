-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 998244353

def solve_ipl_rooms (p q r : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_in_valid_range (p q r : Nat) (h1 : p > 0) (h2 : q > 0) (h3 : r > 0) :
  let result := solve_ipl_rooms p q r
  0 ≤ result ∧ result < MOD :=
sorry

theorem empty_when_insufficient_rooms (p q r : Nat) (h1 : p > 0) (h2 : q > 0) (h3 : r > 0) :
  p + q/2 < r → solve_ipl_rooms p q r = 0 :=
sorry

theorem symmetric_case (n : Nat) (h : n > 0) :
  solve_ipl_rooms n n 1 = solve_ipl_rooms n n 1 :=
sorry
-- </vc-theorems>