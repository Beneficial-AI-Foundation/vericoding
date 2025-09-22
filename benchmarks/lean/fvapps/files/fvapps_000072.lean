-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_non_decreasing (arr : List Nat) : Nat × List Nat := sorry

theorem make_non_decreasing_sorted_array 
  {arr : List Nat} 
  (h : ∀ (i j : Fin arr.length), i.val < j.val → arr[i] ≤ arr[j]) :
  make_non_decreasing arr = (0, []) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem make_non_decreasing_specific_case1 :
  make_non_decreasing [2, 2, 3] = (0, []) := sorry

theorem make_non_decreasing_specific_case2
  {arr : List Nat}
  (h : arr = [2, 1, 0]) :
  (make_non_decreasing arr).2.length ≤ 6 := sorry

theorem make_non_decreasing_specific_case3
  {arr : List Nat}
  (h : arr = [0, 7, 3, 1, 3, 7, 7]) :
  (make_non_decreasing arr).2.length ≤ 14 := sorry
-- </vc-theorems>