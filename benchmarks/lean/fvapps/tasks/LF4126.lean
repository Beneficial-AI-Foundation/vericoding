-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_middle (s : String) : Int := sorry

def isSubstring (needle haystack : String) : Prop := 
  ∃ pre suf, haystack = pre ++ needle ++ suf
-- </vc-definitions>

-- <vc-theorems>
theorem find_middle_two_digits (d1 d2 : Nat) (h1 : d1 > 0) (h2 : d1 < 10) (h3 : d2 > 0) (h4 : d2 < 10) :
  find_middle s!"a{d1}b{d2}c" = d1 * d2 := sorry
-- </vc-theorems>