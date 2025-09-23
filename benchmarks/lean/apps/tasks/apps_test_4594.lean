-- <vc-preamble>
def ValidInput (diameters : List Int) : Prop :=
  diameters.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < diameters.length → diameters[i]! > 0

def num_distinct (s : List Int) : Int :=
  if s.length = 0 then 0
  else if s.head! ∈ s.tail then num_distinct s.tail
  else 1 + num_distinct s.tail
  termination_by s.length

@[reducible, simp]
def solve_precond (diameters : List Int) : Prop :=
  ValidInput diameters
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (diameters : List Int) (h_precond : solve_precond diameters) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (diameters : List Int) (result : Int) (h_precond : solve_precond diameters) : Prop :=
  result = num_distinct diameters ∧ result ≥ 1 ∧ result ≤ diameters.length

theorem solve_spec_satisfied (diameters : List Int) (h_precond : solve_precond diameters) :
    solve_postcond diameters (solve diameters h_precond) h_precond := by
  sorry
-- </vc-theorems>