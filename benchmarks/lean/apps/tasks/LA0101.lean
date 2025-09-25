-- <vc-preamble>
def sumRange (s : List Int) (start : Nat) (end_ : Nat) : Int :=
  if start >= end_ then 
    0
  else if start >= s.length then
    0
  else 
    s[start]! + sumRange s (start + 1) end_

def ValidInput (n : Int) (years : List Int) : Prop :=
  n > 0 ∧ years.length = n.natAbs

@[reducible, simp]
def solve_precond (n : Int) (years : List Int) : Prop :=
  ValidInput n years
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (years : List Int) (h_precond : solve_precond n years) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (years : List Int) (result : Int) (h_precond : solve_precond n years) : Prop :=
  result = sumRange years 0 years.length / n

theorem solve_spec_satisfied (n : Int) (years : List Int) (h_precond : solve_precond n years) :
    solve_postcond n years (solve n years h_precond) h_precond := by
  sorry
-- </vc-theorems>