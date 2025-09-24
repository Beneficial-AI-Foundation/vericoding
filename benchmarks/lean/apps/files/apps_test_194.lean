-- <vc-preamble>
def ValidInput (n : Int) (a : Int) (b : Int) (groups : List Int) : Prop :=
  n ≥ 1 ∧ a ≥ 1 ∧ b ≥ 1 ∧ groups.length = n ∧
  ∀ i, 0 ≤ i ∧ i < groups.length → groups[i]! = 1 ∨ groups[i]! = 2

def countDeniedPeopleWithHalf (groups : List Int) (a : Int) (b : Int) (halfOccupied : Int) : Int :=
  match groups with
  | [] => 0
  | group :: rest =>
    if group = 2 then
      if b > 0 then countDeniedPeopleWithHalf rest a (b - 1) halfOccupied
      else 2 + countDeniedPeopleWithHalf rest a b halfOccupied
    else
      if a > 0 then countDeniedPeopleWithHalf rest (a - 1) b halfOccupied
      else if b > 0 then countDeniedPeopleWithHalf rest a (b - 1) (halfOccupied + 1)
      else if halfOccupied > 0 then countDeniedPeopleWithHalf rest a b (halfOccupied - 1)
      else 1 + countDeniedPeopleWithHalf rest a b halfOccupied
termination_by groups.length

def countDeniedPeople (groups : List Int) (a : Int) (b : Int) : Int :=
  countDeniedPeopleWithHalf groups a b 0

@[reducible, simp]
def solve_precond (n : Int) (a : Int) (b : Int) (groups : List Int) : Prop :=
  ValidInput n a b groups
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : Int) (b : Int) (groups : List Int) (h_precond : solve_precond n a b groups) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : Int) (b : Int) (groups : List Int) (denied : Int) (h_precond : solve_precond n a b groups) : Prop :=
  denied ≥ 0 ∧ denied = countDeniedPeople groups a b

theorem solve_spec_satisfied (n : Int) (a : Int) (b : Int) (groups : List Int) (h_precond : solve_precond n a b groups) :
    solve_postcond n a b groups (solve n a b groups h_precond) h_precond := by
  sorry
-- </vc-theorems>