-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length = 3 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = 'S' ∨ s.data[i]! = 'R'

def MaxConsecutiveRainyDays (s : String) : Int :=
  if s = "RRR" then 3
  else if s.take 2 = "RR" ∨ s.drop 1 = "RR" then 2
  else if s.contains 'R' then 1
  else 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : Int) (h_precond : solve_precond input) : Prop :=
  result = MaxConsecutiveRainyDays input ∧ 0 ≤ result ∧ result ≤ 3

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>