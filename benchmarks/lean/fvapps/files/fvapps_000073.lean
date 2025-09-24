-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def merge_sorted_arrays (a1 a2 : List Int) : List Int := sorry

theorem merge_sorted_arrays_case1 :
  merge_sorted_arrays [2, 1, 2] [1, -1, 5] = [2, 1, -1, 5] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem merge_sorted_arrays_case2 :
  merge_sorted_arrays [1, 2, 3] [4, 5, 6] = [1, 2, 3, 4, 5, 6] := sorry
-- </vc-theorems>