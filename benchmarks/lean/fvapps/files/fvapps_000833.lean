-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseString (s : String) : String := sorry

theorem reverse_twice_is_original (s : String) :
  reverseString (reverseString s) = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_preserves_length (s : String) :
  (reverseString s).length = s.length := sorry

theorem first_last_swap (s : String) (h : s.length > 0) :
  (reverseString s).front = s.back ∧ 
  (reverseString s).back = s.front := sorry

-- Note: The sorted property is harder to express in Lean's type system
-- as it requires defining what "sorted" means for strings and proving
-- permutation properties. A simplified version could be:

theorem reverse_preserves_chars (s : String) (c : Char) :
  s.contains c ↔ (reverseString s).contains c := sorry
-- </vc-theorems>