def isAlpha (c : Char) : Bool := sorry
def isDigit (c : Char) : Bool := sorry

def reformat (s : String) : String := sorry

theorem reformat_empty_string (s : String) : 
  let letters := s.data.filter isAlpha |>.length
  let digits := s.data.filter isDigit |>.length
  letters - digits > 1 ∨ digits - letters > 1 →
  reformat s = "" := sorry

def countLetters (s : String) : Nat :=
  s.data.filter isAlpha |>.length

-- <vc-helpers>
-- </vc-helpers>

def countDigits (s : String) : Nat :=
  s.data.filter isDigit |>.length

theorem reformat_preserves_length (s : String) :
  reformat s ≠ "" → 
  (reformat s).length = s.length := sorry 

theorem reformat_preserves_chars (s : String) :
  reformat s ≠ "" →
  (reformat s).data = s.data := sorry

theorem reformat_alternates (s : String) :
  reformat s ≠ "" →
  ∀ i < (reformat s).length - 1,
    (isAlpha ((reformat s).data[i]!) = !isAlpha ((reformat s).data[i+1]!)) := sorry

theorem reformat_preserves_letter_count (s : String) :
  reformat s ≠ "" →
  countLetters (reformat s) = countLetters s := sorry

theorem reformat_preserves_digit_count (s : String) :
  reformat s ≠ "" →
  countDigits (reformat s) = countDigits s := sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval reformat "leetcode"

-- Apps difficulty: introductory
-- Assurance level: unguarded