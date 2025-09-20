-- <vc-preamble>
def MOD := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_messi_passing (n_passes: Nat) (k_teammates: Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_passes_equals_teammates {k: Nat} (h: k ≤ 1000) (h2: k ≥ 1) :
  solve_messi_passing 2 k = k :=
sorry

theorem result_bounded_by_power {n k: Nat} (h1: n ≥ 2) (h2: n ≤ 1000)
    (h3: k ≥ 1) (h4: k ≤ 1000) :
  solve_messi_passing n k ≤ k^(n-1) :=
sorry
-- </vc-theorems>