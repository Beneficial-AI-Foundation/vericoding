-- <vc-preamble>
def Factorial (n : Nat) : Nat :=
if n = 0 then 1 else n * Factorial (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IterativeFactorial (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IterativeFactorial_spec (n : Nat) :
IterativeFactorial n = Factorial n :=
sorry
-- </vc-theorems>