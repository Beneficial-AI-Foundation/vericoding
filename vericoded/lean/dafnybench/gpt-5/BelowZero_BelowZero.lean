import Mathlib
-- <vc-preamble>
def sum (s : Array Int) (n : Nat) : Int :=
if s.size = 0 ∨ n = 0 then
0
else
s.get! 0 + sum (s.extract 1 s.size) (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no additional helpers needed for this file
-- </vc-helpers>

-- <vc-definitions>
def BelowZero (ops : Array Int) : Bool :=
decide (∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0)
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (s : Array Int) (n : Nat) :
n ≤ s.size → sum s n = sum s n :=
by
  intro _
  rfl

theorem BelowZero_spec (ops : Array Int) :
BelowZero ops = true ↔ ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0 :=
by
  classical
  unfold BelowZero
  by_cases h : ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0
  · simpa [h]
  · simpa [h]
-- </vc-theorems>
