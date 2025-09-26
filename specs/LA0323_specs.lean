-- <vc-preamble>
def LastOccurrenceHelper (cafes : List Int) (cafe : Int) (index : Nat) : Int :=
  if index ≥ cafes.length then
    -1
  else if cafes[index]! = cafe then
    Int.ofNat index
  else if index = 0 then
    -1
  else
    LastOccurrenceHelper cafes cafe (index - 1)
termination_by index

def LastOccurrencePosition (cafes : List Int) (cafe : Int) : Int :=
  if cafes.length = 0 then
    -1
  else
    LastOccurrenceHelper cafes cafe (cafes.length - 1)

@[reducible, simp]
def solve_precond (cafes : List Int) : Prop :=
  cafes.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (cafes : List Int) (h_precond : solve_precond cafes) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (cafes : List Int) (mini : Int) (h_precond : solve_precond cafes) : Prop :=
  mini ∈ cafes ∧ 
  ∀ cafe, cafe ∈ cafes → LastOccurrencePosition cafes mini ≤ LastOccurrencePosition cafes cafe

theorem solve_spec_satisfied (cafes : List Int) (h_precond : solve_precond cafes) :
    solve_postcond cafes (solve cafes h_precond) h_precond := by
  sorry
-- </vc-theorems>