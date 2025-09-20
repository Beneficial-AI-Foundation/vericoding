-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def solve_yalalovichik (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_identity (c : Char) (h : c.isDigit) :
  solve_yalalovichik (String.mk [c]) = c.toNat - '0'.toNat := sorry
-- </vc-theorems>