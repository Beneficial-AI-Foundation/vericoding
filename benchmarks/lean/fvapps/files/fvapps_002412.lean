-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_common_prefix (strs : List String) : String := sorry

def min (a b : Nat) : Nat := if a ≤ b then a else b
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_returns_empty :
  longest_common_prefix [] = "" := sorry

theorem single_string_returns_self (s : String) :
  longest_common_prefix [s] = s := sorry

theorem result_is_prefix_of_all {strs : List String} (h : strs ≠ []) :
  ∀ s ∈ strs, longest_common_prefix strs = s.take (longest_common_prefix strs).length := sorry

theorem not_longer_than_shortest {strs : List String} (h : strs ≠ []) :
  (longest_common_prefix strs).length ≤ List.foldl min (String.length (List.get! strs 0)) (strs.map String.length) := sorry

theorem different_prefix_shortens {strs : List String} (h₁ : strs ≠ [])
  (h₂ : (longest_common_prefix strs).length > 0) (different_prefix : String) :
  (longest_common_prefix (strs ++ ["x" ++ different_prefix])).length < (longest_common_prefix strs).length := sorry

theorem substring_of_first {strs : List String} (h : strs ≠ []) :
  longest_common_prefix strs = (List.get! strs 0).take (longest_common_prefix strs).length := sorry
-- </vc-theorems>