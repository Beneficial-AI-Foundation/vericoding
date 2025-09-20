-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_construct (ransomNote magazine : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_construct_empty_note (magazine : String) :
  can_construct "" magazine = true := sorry

theorem can_construct_empty_magazine_only_empty_note :
  (can_construct "" "" = true) ∧ (can_construct "a" "" = false) := sorry

theorem can_construct_length_property (note magazine : String) :
  note.length > magazine.length → can_construct note magazine = false := sorry

theorem can_construct_same_string (s : String) :
  can_construct s s = true := sorry

theorem can_construct_count_preservation (note magazine : String) (c : Char) :
  can_construct note magazine = true →
  note.data.foldl (λ acc x => if x = c then acc + 1 else acc) 0 ≤ 
  magazine.data.foldl (λ acc x => if x = c then acc + 1 else acc) 0 := sorry

theorem can_construct_magazine_extension (note magazine extension : String) :
  can_construct note magazine = true →
  can_construct note (magazine ++ extension) = true := sorry
-- </vc-theorems>