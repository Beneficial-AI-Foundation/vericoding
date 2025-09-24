-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def summation (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem summation_formula (n : Nat) (h : n > 0) : 
  summation n = n * (n + 1) / 2 := 
  sorry

theorem summation_increasing {a b : Nat} (ha : a > 0) (hb : b > 0) :
  summation (a + b) > summation a :=
  sorry
-- </vc-theorems>