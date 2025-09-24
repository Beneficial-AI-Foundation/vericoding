-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def count_substring_appearances (n: Nat) (strings: List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_substring_output_length {n: Nat} {strings: List String} :
  strings ≠ [] →
  List.length (count_substring_appearances n strings) = List.length strings :=
  sorry

theorem count_substring_long_string_zero {n: Nat} {s: String} {strings: List String} :  
  String.length s > n →
  s ∈ strings → 
  ∃ i, i < List.length strings ∧ 
    (List.get! (count_substring_appearances n strings) i) = 0 :=
  sorry

theorem count_substring_empty_list {n: Nat} : 
  count_substring_appearances n [] = [] :=
  sorry

theorem count_substring_min_n :
  count_substring_appearances 1 ["a"] = [1] ∧
  count_substring_appearances 1 ["aa"] = [0] :=
  sorry
-- </vc-theorems>