-- <vc-preamble>
def ValidInput (skills : List Int) : Prop :=
  skills.length ≥ 0

def HasAdjacentSkills (skills : List Int) : Prop :=
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < skills.length ∧ (skills[i]! - skills[j]! = 1 ∨ skills[j]! - skills[i]! = 1)

@[reducible, simp]
def solve_precond (skills : List Int) : Prop :=
  ValidInput skills
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (skills : List Int) (h_precond : solve_precond skills) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (skills : List Int) (teams : Int) (h_precond : solve_precond skills) : Prop :=
  (teams = 1 ∨ teams = 2) ∧ 
  (teams = 2 ↔ HasAdjacentSkills skills) ∧
  (teams = 1 ↔ ¬HasAdjacentSkills skills)

theorem solve_spec_satisfied (skills : List Int) (h_precond : solve_precond skills) :
    solve_postcond skills (solve skills h_precond) h_precond := by
  sorry
-- </vc-theorems>