-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_multiset_averages (N K M : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem common_moduli {N K : Nat} (h1 : N > 0) (h2 : K > 0) :
  let primes := [998244353, 1000000007]
  ∀ M ∈ primes,
    ∀ x ∈ solve_multiset_averages N K M,
      0 ≤ x ∧ x < M :=
  sorry

theorem edge_case_n1 :
  (solve_multiset_averages 1 1 (10^9 + 7)).length = 1 :=
  sorry

theorem edge_case_min_input :
  let result := solve_multiset_averages 1 1 2
  result.length = 1 ∧ result.head! < 2 :=
  sorry
-- </vc-theorems>