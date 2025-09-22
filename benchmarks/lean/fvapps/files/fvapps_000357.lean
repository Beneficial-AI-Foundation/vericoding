-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_substring_with_k_occurrences (s : String) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (s : String) (k : Nat) 
  (h1 : s.length > 0) (h2 : k > 0) (h3 : k ≤ 10) :
  let result := longest_substring_with_k_occurrences s k
  0 ≤ result ∧ result ≤ s.length :=
  sorry

theorem singleton_strings_k_one (s : String) (k : Nat)
  (h1 : s.length = 1) (h2 : k = 1) :
  longest_substring_with_k_occurrences s k = 1 :=
  sorry

theorem singleton_strings_k_gt_one (s : String) (k : Nat)
  (h1 : s.length = 1) (h2 : k > 1) :
  longest_substring_with_k_occurrences s k = 0 :=
  sorry
-- </vc-theorems>