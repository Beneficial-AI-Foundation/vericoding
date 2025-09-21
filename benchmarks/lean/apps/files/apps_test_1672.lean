-- <vc-preamble>
def ValidInput (magnets : List String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < magnets.length → magnets[i]! = "01" ∨ magnets[i]! = "10"

def CountGroups (magnets : List String) : Nat :=
  if magnets.length = 0 then 0
  else 1 + (List.range magnets.length |>.filter (fun i => 1 ≤ i ∧ i < magnets.length ∧ magnets[i]! ≠ magnets[i-1]!)).length

@[reducible, simp]
def solve_precond (magnets : List String) : Prop :=
  ValidInput magnets
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (magnets : List String) (h_precond : solve_precond magnets) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (magnets : List String) (result : Nat) (h_precond : solve_precond magnets) : Prop :=
  result ≥ 0 ∧
  (magnets.length = 0 → result = 0) ∧
  (magnets.length > 0 → result ≥ 1) ∧
  result ≤ magnets.length ∧
  result = CountGroups magnets

theorem solve_spec_satisfied (magnets : List String) (h_precond : solve_precond magnets) :
    solve_postcond magnets (solve magnets h_precond) h_precond := by
  sorry
-- </vc-theorems>