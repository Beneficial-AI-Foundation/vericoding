import Mathlib
-- <vc-preamble>
def sum (s : Array Int) (n : Nat) : Int :=
if s.size = 0 ∨ n = 0 then
0
else
s[0]! + sum (s.extract 1 s.size) (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed.
-- </vc-helpers>

-- <vc-definitions>
def below_zero (ops : Array Int) : Bool :=
if h : ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0 then true else false
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (s : Array Int) (n : Nat) :
n ≤ s.size → sum s n = sum s n :=
by
  intro _h
  rfl

theorem below_zero_spec (ops : Array Int) :
below_zero ops = true ↔ ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0 :=
by
  classical
  by_cases h : ∃ n : Nat, n ≤ ops.size ∧ sum ops n < 0
  · simp [below_zero, h]
  · simp [below_zero, h]
-- </vc-theorems>
