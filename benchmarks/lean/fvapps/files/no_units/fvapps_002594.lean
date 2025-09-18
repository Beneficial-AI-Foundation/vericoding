-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def missing_alphabets (s : String) : String := sorry

def counts_for_char (s : String) (c : Char) : Nat :=
  s.data.count c
-- </vc-definitions>

-- <vc-theorems>
theorem missing_alphabets_result_lowercase (s : String) (h : s.length > 0) :
  let result := missing_alphabets s
  ∀ c, c ∈ result.data → c.isLower := sorry 

theorem missing_alphabets_equalizes_counts (s : String) (h : s.length > 0) :
  let result := missing_alphabets s
  let combined := s ++ result
  ∃ max_count : Nat, ∀ c, c.isLower → 
    counts_for_char combined c = max_count ∨ counts_for_char combined c = 0 := sorry

theorem missing_alphabets_only_non_max (s : String) (h : s.length > 0) :
  let result := missing_alphabets s
  ∃ max_input_count : Nat, 
    (∀ c, c.isLower → counts_for_char s c ≤ max_input_count) ∧
    (∀ c ∈ result.data, counts_for_char s c < max_input_count) := sorry
-- </vc-theorems>