-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_apple_distribution (n k : Nat) : String := sorry

theorem apple_distribution_property {n k : Nat} (hn : n > 0) (hk : k > 0) :
  solve_apple_distribution n k = "YES" ∨ solve_apple_distribution n k = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem apple_distribution_div_condition {n k : Nat} (hn : n > 0) (hk : k > 0)
  (h1 : n % k = 0) (h2 : (n / k) % k = 0) :
  solve_apple_distribution n k = "NO" := sorry

theorem single_box_distribution {n : Nat} (h : n > 0) :
  solve_apple_distribution n 1 = "NO" := sorry

theorem edge_case_minimum :
  solve_apple_distribution 1 1 = "NO" := sorry
-- </vc-theorems>