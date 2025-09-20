-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) : Int :=
  sorry

def minimum (a x : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimum_makes_number_divisible (a x : Int) (h : x ≠ 0) :
  (a + minimum a x) % x = 0 ∨ (a - minimum a x) % x = 0 :=
sorry
-- </vc-theorems>