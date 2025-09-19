-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def List.sort (l: List Nat) : List Nat :=
  sorry

def solve_minimized_workload (n: Nat) (p: Nat) (workloads: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem workload_result_bounds (n p: Nat) (workloads: List Nat)
  (h1: n > 0) (h2: n ≤ 100) (h3: p > 0) (h4: p ≤ 10)
  (h5: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h6: workloads.length > 0) (h7: workloads.length ≤ 100) :
  let result := solve_minimized_workload n p workloads
  0 ≤ result ∧ result < MOD :=
sorry

theorem workload_p_one_special_case (n p: Nat) (workloads: List Nat)
  (h1: n > 0) (h2: n ≤ 100) (h3: p = 1)
  (h4: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h5: workloads.length > 0) (h6: workloads.length ≤ 100) :
  let result := solve_minimized_workload n p workloads
  result = n % 2 ∧ (result = 0 ∨ result = 1) :=
sorry

theorem workload_sort_invariant (n p: Nat) (workloads: List Nat)
  (h1: n > 0) (h2: n ≤ 100) (h3: p > 0) (h4: p ≤ 10)
  (h5: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h6: workloads.length > 0) (h7: workloads.length ≤ 100) :
  solve_minimized_workload n p workloads =
  solve_minimized_workload n p (List.sort workloads) :=
sorry

theorem workload_length_matches_n (p: Nat) (workloads: List Nat)
  (h1: p > 0) (h2: p ≤ 10)
  (h3: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h4: workloads.length > 0) (h5: workloads.length ≤ 100) :
  let n := workloads.length
  let result := solve_minimized_workload n p workloads
  0 ≤ result ∧ result < MOD :=
sorry
-- </vc-theorems>