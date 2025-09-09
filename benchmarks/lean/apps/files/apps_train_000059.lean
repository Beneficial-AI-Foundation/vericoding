-- <vc-helpers>
-- </vc-helpers>

def solve_array_differences (n : Nat) (arr : List Int) : Int × Int := sorry

/- Properties for all-negative-ones case -/

theorem all_neg_ones_result {n : Nat} {arr : List Int} 
  (h : ∀ x ∈ arr, x = -1) :
  solve_array_differences n arr = (0, 0) := sorry

/- Main property about adjacent differences being bounded by result -/

theorem adjacent_differences_bounded {n : Nat} {arr : List Int} :
  let (ans, x) := solve_array_differences n arr
  ∀ i < arr.length - 1,
    arr[i]! ≠ -1 → arr[i+1]! ≠ -1 → 
    (arr[i]! - arr[i+1]!).natAbs ≤ ans := sorry

/- Property about the x value working for -1 positions -/

theorem x_value_maintains_bound {n : Nat} {arr : List Int} :
  let (ans, x) := solve_array_differences n arr
  ∀ i < arr.length,
    arr[i]! = -1 →
    (i > 0 → arr[i-1]! ≠ -1 → (arr[i-1]! - x).natAbs ≤ ans) ∧
    (i < arr.length - 1 → arr[i+1]! ≠ -1 → (x - arr[i+1]!).natAbs ≤ ans) := sorry

/- Property about result types and non-negativity -/

theorem result_properties {n : Nat} {arr : List Int} :
  let (ans, x) := solve_array_differences n arr
  ans ≥ 0 := sorry

/-
info: (1, 11)
-/
-- #guard_msgs in
-- #eval solve_array_differences 5 [-1, 10, -1, 12, -1]

/-
info: (0, 0)
-/
-- #guard_msgs in
-- #eval solve_array_differences 2 [-1, -1]

/-
info: (1, 2)
-/
-- #guard_msgs in
-- #eval solve_array_differences 4 [1, -1, 3, -1]

-- Apps difficulty: interview
-- Assurance level: unguarded