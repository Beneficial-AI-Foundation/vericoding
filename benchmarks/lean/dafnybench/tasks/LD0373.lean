-- <vc-preamble>
def NChoose2 (n : Int) : Int :=
n * (n - 1) / 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BubbleSort (a : Array Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bubbleSort_spec (a : Array Int) (n : Nat) :
n ≤ NChoose2 a.size :=
sorry
-- </vc-theorems>