import Mathlib
-- <vc-preamble>
partial def Factorial (n : Nat) : Nat :=
if n == 0 then 1 else n * Factorial (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper lemmas required for this development.
-- </vc-helpers>

-- <vc-definitions>
def ComputeFactorial (n : Int) : Int :=
(Factorial n.toNat : Int)
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeFactorial_spec (n : Int) :
1 ≤ n → ComputeFactorial n = Factorial n.toNat :=
by
  intro _
  rfl
-- </vc-theorems>
