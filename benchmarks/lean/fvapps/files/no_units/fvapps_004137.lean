-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_or_even (nums : List Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_or_even_result_valid (nums : List Int) :
  (odd_or_even nums = "odd") ∨ (odd_or_even nums = "even") :=
  sorry

theorem odd_or_even_matches_sum (nums : List Int) :
  odd_or_even nums = (if (nums.foldl (· + ·) 0) % 2 = 0 then "even" else "odd") :=
  sorry

theorem empty_equals_zero :
  odd_or_even [] = odd_or_even [0] := 
  sorry

theorem odd_or_even_concatenation (nums1 nums2 : List Int) 
  (h1 : nums1 ≠ []) (h2 : nums2 ≠ []) :
  odd_or_even (nums1 ++ nums2) = 
    if odd_or_even nums1 = odd_or_even nums2 
    then "even" 
    else "odd" :=
  sorry
-- </vc-theorems>