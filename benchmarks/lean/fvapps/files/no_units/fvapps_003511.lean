-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tiy_fizz_buzz (s : String) : String := sorry

def isSubstringOf (needle haystack : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_never_shorter (s : String) :
  (tiy_fizz_buzz s).length ≥ s.length := sorry

theorem preserves_non_letters (s : String) (c : Char) :
  c ∈ s.data → ¬c.isAlpha → c.toNat < 128 → c ∈ (tiy_fizz_buzz s).data := sorry 

theorem uppercase_becomes_iron (s : String) (c : Char) :  
  c ∈ s.data → c.isUpper → isSubstringOf "Iron" (tiy_fizz_buzz s) = true := sorry

theorem vowels_become_yard (s : String) (c : Char) :
  c ∈ s.data → c.toLower ∈ ['a', 'e', 'i', 'o', 'u'] → 
  isSubstringOf "Yard" (tiy_fizz_buzz s) = true := sorry
-- </vc-theorems>