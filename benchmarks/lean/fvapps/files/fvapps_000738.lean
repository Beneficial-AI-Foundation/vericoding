-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def VOWELS := ["A", "E", "I", "O", "U"]

def is_clingy (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uppercase_letters (s : String) (h : s.all Char.isUpper) : 
  is_clingy s = true ∨ is_clingy s = false := sorry

theorem rotations_equivalent (s : String) (i : Nat) (h : i < s.length) :
  is_clingy s = is_clingy (s.drop i ++ s.take i) := sorry

theorem all_vowels_clingy (s : String) 
  (h1 : s.all (fun c => c.toString ∈ VOWELS))
  (h2 : s.length ≥ 2) :
  is_clingy s = true := sorry

theorem consonants_not_clingy (s : String)
  (h : s.all (fun c => c.toString ∉ VOWELS)) :
  is_clingy s = false := sorry

theorem single_char_not_clingy (c : Char) 
  (h : c.isUpper) :
  is_clingy c.toString = false := sorry
-- </vc-theorems>