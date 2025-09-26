-- <vc-preamble>
def ValidOutput (names : List String) (output : List String) : Prop :=
  output.length = names.length ∧
  ∀ i, 0 ≤ i ∧ i < names.length → 
    output.get! i = (if (List.range i).any (fun j => names.get! j = names.get! i) then "YES" else "NO")

@[reducible, simp]
def solve_precond (names : List String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (names : List String) (h_precond : solve_precond names) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (names : List String) (result : List String) (h_precond : solve_precond names) : Prop :=
  ValidOutput names result

theorem solve_spec_satisfied (names : List String) (h_precond : solve_precond names) :
    solve_postcond names (solve names h_precond) h_precond := by
  sorry
-- </vc-theorems>