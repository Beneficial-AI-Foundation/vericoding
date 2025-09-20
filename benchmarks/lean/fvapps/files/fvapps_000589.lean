-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_impact_points (N : Nat) (K : Nat) (M : Nat) (X0 : Nat) : String := sorry

theorem solve_impact_points_returns_valid_output 
  (N : Nat) (K : Nat) (M : Nat) (X0 : Nat)
  (hN : 1 ≤ N ∧ N ≤ 1000)
  (hK : 1 ≤ K ∧ K ≤ 10) 
  (hM : 0 ≤ M ∧ M ≤ 1000)
  (hX0 : 0 ≤ X0 ∧ X0 ≤ 1000) :
  solve_impact_points N K M X0 = "yes" ∨ 
  solve_impact_points N K M X0 = "no" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem k_equals_one_property
  (N : Nat) (M : Nat) (X0 : Nat)
  (hN : 1 ≤ N ∧ N ≤ 1000)
  (hM : 0 ≤ M ∧ M ≤ 1000)
  (hX0 : 0 ≤ X0 ∧ X0 ≤ 1000) :
  solve_impact_points N 1 M X0 = (if N = M then "yes" else "no") := sorry

theorem k_two_three_property_mod
  (N : Nat) (K : Nat) (M : Nat) (X0 : Nat)
  (hN : 1 ≤ N ∧ N ≤ 100)
  (hK : K = 2 ∨ K = 3)
  (hM : 0 ≤ M ∧ M ≤ 100)
  (hX0 : 0 ≤ X0 ∧ X0 ≤ 100)
  (hmod : M % K > 1) :
  solve_impact_points N K M X0 = "no" := sorry

theorem k_three_digit_property
  (N : Nat) (M : Nat) (X0 : Nat)
  (hN : 1 ≤ N ∧ N ≤ 100)
  (hM : 0 ≤ M ∧ M ≤ 100)
  (hX0 : 0 ≤ X0 ∧ X0 ≤ 100)
  (hdigit : ∃ d, d > 2 ∧ ∃ k, M = d + 3 * k) :
  solve_impact_points N 3 M X0 = "no" := sorry

theorem x0_invariant
  (N : Nat) (K : Nat) (M : Nat) (X0_1 X0_2 : Nat)
  (hN : 1 ≤ N ∧ N ≤ 100)
  (hK : 1 ≤ K ∧ K ≤ 10)
  (hM : 0 ≤ M ∧ M ≤ 100)
  (hX0_1 : 0 ≤ X0_1 ∧ X0_1 ≤ 100)
  (hX0_2 : 0 ≤ X0_2 ∧ X0_2 ≤ 100) :
  solve_impact_points N K M X0_1 = solve_impact_points N K M X0_2 := sorry
-- </vc-theorems>