-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_paths (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_paths_nonnegative (n : Nat) :
  count_paths n ≥ 0 ∧ count_paths n % 2 = 0 :=
sorry 

theorem count_paths_zero :
  count_paths 0 = 0 :=
sorry

theorem count_paths_monotonic {n : Nat} (h : n > 0) :
  count_paths n > count_paths (n-1) :=
sorry

theorem count_paths_superlinear {n : Nat} (h1 : n > 1) :
  count_paths n / count_paths (n-1) > 1 :=
sorry
-- </vc-theorems>