-- <vc-preamble>
partial def Factorial (n : Int) : Int :=
if n == 0 then 1
else n * Factorial (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FactorialOfLastDigit (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Factorial_spec (n : Int) :
n ≥ 0 → Factorial n ≥ 0 :=
sorry

theorem FactorialOfLastDigit_spec (n : Int) :
n ≥ 0 → FactorialOfLastDigit n = Factorial (n % 10) :=
sorry
-- </vc-theorems>