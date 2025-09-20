-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countSubarraysWithSum (nums : List Int) (k : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_property (k : Int) :
  countSubarraysWithSum [] k = 0 := by
  sorry

theorem single_element_property (x k : Int) :
  countSubarraysWithSum [x] k = if x = k then 1 else 0 := by
  sorry

theorem uniform_array_property {x : Int} {len : Nat} {arr : List Int} 
    (h1 : len > 0)
    (h2 : arr = List.replicate len x) :
    x ≠ 0 → len ≥ 2 → countSubarraysWithSum arr (2*x) > 0 := by
  sorry

theorem uniform_zeros_property {len : Nat} {arr : List Int}
    (h1 : len > 0)
    (h2 : arr = List.replicate len 0) :
    countSubarraysWithSum arr 0 = len * (len + 1) / 2 := by
  sorry

theorem non_negative_result_property (nums : List Int) (k : Int) :
  countSubarraysWithSum nums k ≥ 0 := by
  sorry

theorem reverse_invariant_property (nums : List Int) (k : Int) :
  countSubarraysWithSum nums k = countSubarraysWithSum (List.reverse nums) k := by
  sorry
-- </vc-theorems>