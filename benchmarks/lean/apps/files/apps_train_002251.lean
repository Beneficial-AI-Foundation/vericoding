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

/-
info: [1, 3, 1]
-/
-- #guard_msgs in
-- #eval solve_multiset_averages 3 1 998244353

/-
info: [2]
-/
-- #guard_msgs in
-- #eval solve_multiset_averages 1 2 1000000007

/-
info: [1, 1]
-/
-- #guard_msgs in
-- #eval solve_multiset_averages 2 1 905589253
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible