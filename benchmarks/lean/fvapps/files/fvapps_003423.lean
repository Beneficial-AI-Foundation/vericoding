-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_onion_array : List Int → Bool :=
  fun _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem onion_array_valid {arr : List Int} 
  (h : ∃ xs, arr = xs ++ List.replicate (xs.length % 2) 0 ++ (xs.map (fun x => 10 - x)).reverse) : 
  is_onion_array arr = true := sorry

theorem empty_single_onion {arr : List Int} (h : arr.length ≤ 1) : 
  is_onion_array arr = true := sorry 

theorem large_nums_not_onion {arr : List Int} 
  (h1 : arr.length ≥ 2) 
  (h2 : ∀ x ∈ arr, x > 10) : 
  is_onion_array arr = false := sorry

theorem onion_symmetric {arr : List Int} :
  is_onion_array arr = is_onion_array arr.reverse := sorry
-- </vc-theorems>