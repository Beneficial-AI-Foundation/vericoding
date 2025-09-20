-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstDup (s : String) : Option Char := sorry

theorem first_dup_result_in_string {s : String} :
  match firstDup s with
  | none => True 
  | some c => s.data.contains c
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_dup_has_multiple_occurrences {s : String} :
  match firstDup s with
  | none => True
  | some c => (s.data.filter (· = c)).length > 1
  := sorry

theorem first_dup_returns_first_duplicate {s : String} (h : s.length > 0) :
  match firstDup s with
  | none => True
  | some c => 
    let firstIdx := s.data.findIdx (· = c)
    ∀ i < firstIdx, ((s.data.take i).filter (· = c)).length ≤ 1
  := sorry

theorem first_dup_valid_chars {s : String} :
  match firstDup s with
  | none => True
  | some c => True
  := sorry
-- </vc-theorems>