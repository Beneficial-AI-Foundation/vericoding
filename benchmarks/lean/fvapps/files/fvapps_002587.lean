-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_largest_sequence (s : String) : Nat :=
  sorry

def isSubstring (sub str : String) : Bool :=
  sorry

def substring (s : String) (start len : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem short_strings (s : String) :
  s.length < 5 → find_largest_sequence s = 0 :=
sorry
-- </vc-theorems>