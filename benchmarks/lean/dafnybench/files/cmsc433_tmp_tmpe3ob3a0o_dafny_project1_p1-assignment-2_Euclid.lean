-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Euclid (m n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Euclid_spec (m n : Int) :
m > 1 ∧ n > 1 ∧ m ≥ n →
let gcd := Euclid m n
gcd > 0 ∧ gcd ≤ n ∧ gcd ≤ m ∧ m % gcd = 0 ∧ n % gcd = 0 :=
sorry
-- </vc-theorems>