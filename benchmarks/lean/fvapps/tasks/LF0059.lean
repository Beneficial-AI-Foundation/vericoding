-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_differences (n : Nat) (arr : List Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_neg_ones_result {n : Nat} {arr : List Int}
  (h : ∀ x ∈ arr, x = -1) :
  solve_array_differences n arr = (0, 0) :=
sorry

theorem adjacent_differences_bounded {n : Nat} {arr : List Int} :
  let (ans, x) := solve_array_differences n arr
  ∀ i < arr.length - 1,
    arr[i]! ≠ -1 → arr[i+1]! ≠ -1 →
    (arr[i]! - arr[i+1]!).natAbs ≤ ans :=
sorry

theorem x_value_maintains_bound {n : Nat} {arr : List Int} :
  let (ans, x) := solve_array_differences n arr
  ∀ i < arr.length,
    arr[i]! = -1 →
    (i > 0 → arr[i-1]! ≠ -1 → (arr[i-1]! - x).natAbs ≤ ans) ∧
    (i < arr.length - 1 → arr[i+1]! ≠ -1 → (x - arr[i+1]!).natAbs ≤ ans) :=
sorry

theorem result_properties {n : Nat} {arr : List Int} :
  let (ans, x) := solve_array_differences n arr
  ans ≥ 0 :=
sorry
-- </vc-theorems>