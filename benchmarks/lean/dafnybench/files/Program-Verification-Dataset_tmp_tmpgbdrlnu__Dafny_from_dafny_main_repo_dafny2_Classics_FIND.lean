-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FIND (A : Array Int) (N : Int) (f : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FIND_spec (A : Array Int) (N : Int) (f : Int) :
A.size = N →
0 ≤ f →
f < N →
∀ p q : Int, 0 ≤ p → p ≤ f → f ≤ q → q < N →
(FIND A N f)[p.toNat]! ≤ (FIND A N f)[q.toNat]! :=
sorry
-- </vc-theorems>