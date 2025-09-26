import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length = 7 ∧ s.data[0]! = 'A' ∧ ∀ i : Nat, 1 ≤ i ∧ i < 7 → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def DigitSum (s : String) (start : Nat) (end_ : Nat) : Nat :=
  if start ≥ end_ then 0
  else s.data[start]!.toNat - '0'.toNat + DigitSum s (start + 1) end_
  termination_by end_ - start

def ZeroCount (s : String) (start : Nat) (end_ : Nat) : Nat :=
  if start ≥ end_ then 0
  else (if s.data[start]! = '0' then 1 else 0) + ZeroCount s (start + 1) end_
  termination_by end_ - start

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper definitions are required for this file.
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Nat :=
  DigitSum s 1 7 + 9 * ZeroCount s 1 7 + 1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Nat) (h_precond : solve_precond s) : Prop :=
  result = DigitSum s 1 7 + 9 * ZeroCount s 1 7 + 1

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
