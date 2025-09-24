-- <vc-preamble>
def triangular_num (n : Nat) : Nat :=
n * (n + 1) / 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_disjoint_subarrays (n : Nat) (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_disjoint_subarrays_output_bounds {n : Nat} {arr : List Nat}
  (hn : n > 0)
  (harr_size : arr.length = n)
  (harr_bounds : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 1000) :
  let result := solve_disjoint_subarrays n arr
  0 ≤ result ∧ result < 1000000007 :=
sorry

theorem solve_disjoint_subarrays_singleton {arr : List Nat}
  (hsingle : arr.length = 1)
  (hbound : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) :
  solve_disjoint_subarrays 1 arr = 1 :=
sorry

theorem solve_disjoint_subarrays_all_equal {n : Nat} {arr : List Nat}
  (hn : n > 1)
  (harr_size : arr.length = n)
  (harr_bounds : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10)
  (hall_equal : ∀ x ∈ arr, x = arr.head!) :
  solve_disjoint_subarrays n arr = (triangular_num n) * (triangular_num n) :=
sorry
-- </vc-theorems>