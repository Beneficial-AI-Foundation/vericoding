-- <vc-preamble>
def isLower (c : Char) : Bool :=
  97 ≤ c.toNat && c.toNat ≤ 122
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alpha_seq (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alpha_seq_parts_sorted {s : String} (h : s ≠ "") : 
  let parts := s.split (· = ',')
  ∀ i j, i < j → j < parts.length → 
    let p1 := (parts[i]?.getD "")
    let p2 := (parts[j]?.getD "")
    p1.length > 0 → p2.length > 0 →
    (p1.data[0]?.getD ' ').toLower ≤ (p2.data[0]?.getD ' ').toLower := by
  sorry 

theorem alpha_seq_parts_capitalized {s : String} (h : s ≠ "") :
  let parts := s.split (· = ',')
  ∀ part ∈ parts, part.length > 0 → 
    part.data[0]?.getD ' ' = (part.data[0]?.getD ' ').toUpper := by
  sorry

theorem alpha_seq_parts_rest_lowercase {s : String} (h : s ≠ "") :
  let parts := s.split (· = ',')
  ∀ part ∈ parts, ∀ i, 0 < i → i < part.length → 
    part.data[i]?.getD ' ' = (part.data[i]?.getD ' ').toLower := by
  sorry

theorem alpha_seq_parts_length {s : String} (h : s ≠ "") :
  let parts := s.split (· = ',')
  ∀ part ∈ parts, part.length > 0 → 
    part.length = (part.data[0]?.getD ' ').toLower.toNat - 96 := by
  sorry

theorem alpha_seq_parts_same_char {s : String} (h : s ≠ "") :
  let parts := s.split (· = ',')
  ∀ part ∈ parts, ∀ i, i < part.length →
    (part.data[i]?.getD ' ').toLower = (part.data[0]?.getD ' ').toLower := by
  sorry
-- </vc-theorems>