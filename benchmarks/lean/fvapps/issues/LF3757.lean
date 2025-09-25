-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSum (arr : List Int) (ranges : List (Nat × Nat)) : Int := sorry

def sumRange (arr : List Int) (start stop : Nat) : Int :=
  (arr.take (stop + 1)).drop start |>.foldl (· + ·) 0
-- </vc-definitions>

-- <vc-theorems>
theorem maxSum_ge_range_sums {arr : List Int} {ranges : List (Nat × Nat)}
    (arr_nonempty : arr.length > 0)
    (ranges_valid : ∀ (r : Nat × Nat), r ∈ ranges → r.2 < arr.length ∧ r.1 ≤ r.2) :
  ∀ (start stop : Nat), (start, stop) ∈ ranges → 
    maxSum arr ranges ≥ sumRange arr start stop
  := sorry

theorem maxSum_equals_max_range_sum {arr : List Int} {ranges : List (Nat × Nat)}
    (arr_nonempty : arr.length > 0)
    (ranges_valid : ∀ (r : Nat × Nat), r ∈ ranges → r.2 < arr.length ∧ r.1 ≤ r.2) :
  maxSum arr ranges = (ranges.map (λ (r : Nat × Nat) => sumRange arr r.1 r.2)).maximum?.getD 0
  := sorry

theorem maxSum_invariant_under_zero_ranges {arr : List Int} {ranges : List (Nat × Nat)}
    (arr_nonempty : arr.length > 0)
    (ranges_valid : ∀ (r : Nat × Nat), r ∈ ranges → r.2 < arr.length ∧ r.1 ≤ r.2)
    (ranges_nonempty : ranges.length > 1) :
  let zero_ranges := ranges ++ (List.range arr.length).map (λ i => (i,i))
  maxSum arr zero_ranges = maxSum arr ranges
  := sorry

theorem maxSum_single_element_ranges {arr : List Int}
    (arr_nonempty : arr.length > 0) :
  let ranges := (List.range arr.length).map (λ i => (i,i))
  maxSum arr ranges = arr.maximum?.getD 0
  := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_sum [1, -2, 3, 4, -5, -4, 3, 2, 1] [[1, 3], [0, 4], [6, 8]]

/-
info: 5
-/
-- #guard_msgs in
-- #eval max_sum [1, -2, 3, 4, -5, -4, 3, 2, 1] [[1, 3]]

/-
info: 88
-/
-- #guard_msgs in
-- #eval max_sum [11, -22, 31, 34, -45, -46, 35, 32, 21] [[1, 4], [0, 3], [6, 8], [0, 8]]
-- </vc-theorems>