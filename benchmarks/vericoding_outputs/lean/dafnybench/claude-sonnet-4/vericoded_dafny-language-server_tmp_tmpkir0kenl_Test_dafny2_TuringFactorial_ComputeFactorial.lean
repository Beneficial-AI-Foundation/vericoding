import Mathlib
-- <vc-preamble>
partial def Factorial (n : Nat) : Nat :=
if n == 0 then 1 else n * Factorial (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def ComputeFactorial (n : Int) : Int :=
if n ≤ 0 then 1 else Factorial n.toNat
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeFactorial_spec (n : Int) :
1 ≤ n → ComputeFactorial n = Factorial n.toNat :=
fun h => by
  simp [ComputeFactorial]
  -- Since h : 1 ≤ n, we have ¬(n ≤ 0)
  have h_pos : ¬(n ≤ 0) := by linarith
  simp [h_pos]
-- </vc-theorems>
