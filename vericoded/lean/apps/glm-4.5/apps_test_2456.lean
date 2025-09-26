import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ValidInput (n r : Int) : Prop :=
  n ≥ 1 ∧ r ≥ 1

def ExpectedResult (n r : Int) (h : ValidInput n r) : Int :=
  let k := if r < n - 1 then r else n - 1
  k * (k + 1) / 2 + (if r ≥ n then 1 else 0)

@[reducible, simp]
def solve_precond (n r : Int) : Prop :=
  ValidInput n r
-- </vc-preamble>

-- <vc-helpers>
-- Helper function for triangular numbers
def triangularNumber (k : Int) : Int :=
  k * (k + 1) / 2

-- Helper function to compute the bounded value k
def computeK (n r : Int) : Int :=
  if r < n - 1 then r else n - 1

-- Helper function to compute the offset
def computeOffset (n r : Int) : Int :=
  if r ≥ n then 1 else 0

-- Lemma that triangularNumber matches the expected formula
lemma triangularNumber_formula (k : Int) :
    triangularNumber k = k * (k + 1) / 2 := by
  rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n r : Int) (h_precond : solve_precond n r) : Int :=
  let k := if r < n - 1 then r else n - 1
  let offset := if r ≥ n then 1 else 0
  k * (k + 1) / 2 + offset
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
