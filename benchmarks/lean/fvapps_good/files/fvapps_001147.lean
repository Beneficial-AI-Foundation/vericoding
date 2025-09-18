-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_subset_problem (N : Nat) (M : Nat) : Nat × Nat := sorry 

theorem subset_problem_output_ranges {N M : Nat} 
  (h1 : N ≥ 1) (h2 : N ≤ 100) 
  (h3 : M ≥ 2) (h4 : M ≤ 10) :
  let (count, perm) := solve_subset_problem N M
  count ≤ N*(N+1)/2 ∧ count ≥ 0 ∧ perm < 998244353 ∧ perm ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>