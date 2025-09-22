-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 3 ∧ s.length ≤ 100 ∧ ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def IntToString (n : Int) : String :=
  toString n

def ValidAbbreviation (s result : String) : Prop :=
  result.length ≥ 3 ∧
  s.length ≥ 3 ∧
  (s.length > 0 → result.data[0]! = s.data[0]!) ∧
  (s.length > 0 ∧ result.length > 0 → result.data[result.length - 1]! = s.data[s.length - 1]!) ∧
  result = String.mk [s.data[0]!] ++ IntToString (s.length - 2) ++ String.mk [s.data[s.length - 1]!]

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  ValidAbbreviation s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>