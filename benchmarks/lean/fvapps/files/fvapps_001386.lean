-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_number (divisors : List Nat) : Nat := sorry

def get_proper_divisors (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_number_preserves_input {divisors original : List Nat} 
  (h : original = divisors) :
  original = divisors := sorry
-- </vc-theorems>