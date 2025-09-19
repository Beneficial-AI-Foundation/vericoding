-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_partition (n : Nat) (arr : List Nat) : Nat := sorry

theorem array_partition_bound {n : Nat} {arr : List Nat} (h : arr.length = 2 * n) :
  let result := solve_array_partition n arr
  0 ≤ result ∧ result < 998244353 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_difference {n : Nat} :
  let arr := List.replicate (2 * n) 1
  solve_array_partition n arr = 0 := sorry

theorem sorted_input_invariant {n : Nat} (arr : List Nat) (h : arr.length = 2 * n) :
  solve_array_partition n arr = solve_array_partition n arr.reverse := sorry

theorem specific_case_1 : solve_array_partition 1 [1, 4] = 6 := sorry

theorem specific_case_2 : solve_array_partition 2 [2, 1, 2, 1] = 12 := sorry

theorem specific_case_3 : solve_array_partition 3 [2, 2, 2, 2, 2, 2] = 0 := sorry
-- </vc-theorems>