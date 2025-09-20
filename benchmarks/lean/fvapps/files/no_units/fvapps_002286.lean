-- <vc-preamble>
def find_median_binary_string (n m : Nat) (removed : List String) : String := sorry

def isAllZeros (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringInList (s : String) (l : List String) : Bool := sorry

def isBinaryChar (c : Char) : Bool :=
  c = '0' || c = '1'

/- The length of the output string matches the input length m -/
-- </vc-definitions>

-- <vc-theorems>
theorem find_median_binary_string_length_matches_input
  {n m : Nat} {removed : List String}
  (h₁ : n < 2^m)
  (h₂ : n = removed.length) :
  (find_median_binary_string n m removed).length = m := sorry
-- </vc-theorems>