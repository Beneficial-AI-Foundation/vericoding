-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximize_weighted_sum (n : Nat) (arr : List Nat) : Nat := sorry

theorem single_element (arr : List Nat) (h : arr.length = 1) :
  maximize_weighted_sum 1 arr = arr[0] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_elements (arr : List Nat) (h : arr.length = 2) :
  maximize_weighted_sum 2 arr = max (arr[0] + 2 * arr[1]) (arr[1] + 2 * arr[0]) := sorry

theorem monotonicity (arr : List Nat) (n : Nat) (h : n = arr.length) (h2 : n > 1) :
  maximize_weighted_sum n arr ≥ maximize_weighted_sum (n-1) (arr.take (n-1)) := sorry
-- </vc-theorems>