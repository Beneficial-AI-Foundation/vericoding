import Mathlib
-- <vc-preamble>
partial def Factorial (n : Nat) : Nat :=
if n == 0 then 1 else n * Factorial (n-1)
-- </vc-preamble>

-- <vc-helpers>


-- </vc-helpers>

-- <vc-definitions>
def ComputeFactorial (n : Int) : Int :=
if 0 ≤ n then
    (Factorial n.toNat : Int)
  else
    1
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeFactorial_spec (n : Int) :
1 ≤ n → ComputeFactorial n = Factorial n.toNat :=
by
  intro hn
  unfold ComputeFactorial
  split_ifs with h
  · rfl
  · linarith [hn, h]
-- </vc-theorems>
