-- <vc-preamble>
def ValidInput (n : Int) (k : Int) (w : List Int) : Prop :=
  k > 0 ∧ n ≥ 0 ∧ w.length = n ∧ ∀ i, 0 ≤ i ∧ i < w.length → w[i]! ≥ 0

def sum_trips (w : List Int) (k : Int) : Int :=
  match w with
  | [] => 0
  | head :: tail => (head + k - 1) / k + sum_trips tail k
termination_by w.length

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (w : List Int) : Prop :=
  ValidInput n k w
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (w : List Int) (h_precond : solve_precond n k w) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (w : List Int) (result : Int) (h_precond : solve_precond n k w) : Prop :=
  result ≥ 0 ∧ result = (sum_trips w k + 1) / 2

theorem solve_spec_satisfied (n : Int) (k : Int) (w : List Int) (h_precond : solve_precond n k w) :
    solve_postcond n k w (solve n k w h_precond) h_precond := by
  sorry
-- </vc-theorems>