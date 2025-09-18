-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def modify_string (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem modify_string_empty : 
  modify_string "" = "" := sorry 

theorem modify_string_no_question_marks {s : String} 
  (h : ∀ c ∈ s.data, 'a' ≤ c ∧ c ≤ 'z') :
  modify_string s = s := sorry

theorem modify_string_length {s : String} :
  (modify_string s).length = s.length := sorry

theorem modify_string_lowercase {s : String} :
  ∀ c ∈ (modify_string s).data, 'a' ≤ c ∧ c ≤ 'z' := sorry

theorem modify_string_no_adjacent_same {s : String} :
  ∀ i, i + 1 < (modify_string s).length → 
    (modify_string s).data[i]! ≠ (modify_string s).data[i+1]! := sorry

theorem modify_string_preserves_non_question {s : String} {i : Nat} :
  i < s.length →
  s.data[i]! ≠ '?' → 
  (modify_string s).data[i]! = s.data[i]! := sorry
-- </vc-theorems>