-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate_hello (s : String) : Bool := sorry

def isSubstrOf (substr str : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validate_hello_case_insensitive (s : String) :
  (∃ x ∈ ["hello", "ciao", "salut", "hallo", "hola", "ahoj", "czesc"], 
    isSubstrOf x s.toLower) ↔ validate_hello s := sorry

theorem validate_hello_with_valid_greeting (greeting : String) (extra : String) 
  (h : greeting ∈ ["hello", "ciao", "salut", "hallo", "hola", "ahoj", "czesc"]) :
  validate_hello (greeting ++ extra) = true := sorry

theorem validate_hello_empty_or_whitespace (s : String) :
  s.trim = "" → validate_hello s = false := sorry
-- </vc-theorems>