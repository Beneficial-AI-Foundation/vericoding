-- <vc-preamble>
def sum (s : Array Int) (n : Nat) : Int :=
if s.size = 0 ∨ n = 0 then
0
else
s.get! 0 + sum (s.extract 1 s.size) (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BelowZero (ops : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (s : Array Int) (n : Nat) :
n ≤ s.size → sum s n = sum s n :=
sorry

theorem BelowZero_spec (ops : Array Int) :
BelowZero ops = true ↔ ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0 :=
sorry
-- </vc-theorems>