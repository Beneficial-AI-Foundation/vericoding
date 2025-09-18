-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_DNA (s1 s2 : String) : Bool := sorry

/- The function check_DNA is symmetric: gives same result regardless of argument order -/
-- </vc-definitions>

-- <vc-theorems>
theorem check_DNA_symmetric (s1 s2 : String) :
  check_DNA s1 s2 = check_DNA s2 s1 := sorry
-- </vc-theorems>