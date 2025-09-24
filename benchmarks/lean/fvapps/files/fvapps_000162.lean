-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubsequence (sub word : String) : Bool := sorry

def find_longest_word (s : String) (dict : List String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_result {dict : List String} : 
  find_longest_word "" dict = "" := sorry

theorem empty_dict_result {s : String} :
  find_longest_word s [] = "" := sorry

theorem result_in_dict {s : String} {dict : List String} :
  let result := find_longest_word s dict
  result ≠ "" → result ∈ dict := sorry

theorem result_is_subsequence {s : String} {dict : List String} :
  let result := find_longest_word s dict
  result ≠ "" → isSubsequence result s = true := sorry

theorem no_longer_valid_word {s : String} {dict : List String} :
  let result := find_longest_word s dict
  ∀ w ∈ dict, w.length > result.length → isSubsequence w s = false := sorry

theorem no_lexically_smaller_valid_word {s : String} {dict : List String} :
  let result := find_longest_word s dict
  ∀ w ∈ dict, w.length = result.length ∧ w < result → isSubsequence w s = false := sorry
-- </vc-theorems>