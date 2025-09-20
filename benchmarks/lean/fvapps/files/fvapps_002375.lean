-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def buddy_strings (s1 s2 : String) : Bool := sorry

theorem buddy_strings_symmetry (s1 s2 : String) : 
  buddy_strings s1 s2 = buddy_strings s2 s1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem buddy_strings_identical_requires_duplicate {s : String} :
  s.length ≥ 2 → 
  let chars := s.data
  let hasDuplicates := ∃ i j, i < j ∧ j < chars.length ∧ chars[i]! = chars[j]!
  buddy_strings s s = hasDuplicates := sorry

theorem buddy_strings_length {s1 s2 : String} :
  s1.length ≠ s2.length ∨ s1.length < 2 →
  ¬(buddy_strings s1 s2) := sorry

theorem single_swap_property {s : String} (h : s.length ≥ 2) :
  let chars := s.data
  let swapped := String.mk (chars.set 0 (chars.get! 1) |>.set 1 (chars.get! 0))
  buddy_strings s swapped := sorry
-- </vc-theorems>