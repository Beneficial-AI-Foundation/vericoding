-- <vc-preamble>
def ValidInput (n : Int) (edges : List (Int × Int)) : Prop :=
  n ≥ 2 ∧
  ∀ i, 0 ≤ i ∧ i < edges.length → 1 ≤ edges[i]!.1 ∧ edges[i]!.1 ≤ n ∧ 1 ≤ edges[i]!.2 ∧ edges[i]!.2 ≤ n ∧ edges[i]!.1 ≠ edges[i]!.2

def ValidOutput (result : Int) (n : Int) (edges : List (Int × Int)) : Prop :=
  result ≥ 0 ∧ result ≤ 2 * edges.length * (edges.length + 1)

@[reducible, simp]
def solve_precond (n : Int) (edges : List (Int × Int)) : Prop :=
  ValidInput n edges
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (edges : List (Int × Int)) (h_precond : solve_precond n edges) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (edges : List (Int × Int)) (result : Int) (h_precond : solve_precond n edges) : Prop :=
  ValidOutput result n edges

theorem solve_spec_satisfied (n : Int) (edges : List (Int × Int)) (h_precond : solve_precond n edges) :
    solve_postcond n edges (solve n edges h_precond) h_precond := by
  sorry
-- </vc-theorems>