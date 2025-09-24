-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_problems (A B C N T : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_problems_equal_values (x N T : Nat)
  (h1 : x > 0) (h2 : N > 0) 
  (h3 : x ≤ 1000) (h4 : N ≤ 1000) (h5 : T ≤ N) :
  solve_problems x x x N T = x * N :=
  sorry

theorem solve_problems_zero_T (A B C N : Nat)
  (h1 : A = 1) (h2 : B = 2) (h3 : C = 3) (h4 : N = 5) :
  solve_problems A B C N 0 = 15 :=
  sorry

theorem solve_problems_full_T (A B C N : Nat)
  (h1 : A = 1) (h2 : B = 2) (h3 : C = 3) (h4 : N = 5) :
  solve_problems A B C N 5 = 5 :=
  sorry
-- </vc-theorems>