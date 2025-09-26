-- <vc-preamble>
def ValidInput (n m k : Int) : Prop :=
  1 ≤ n ∧ n ≤ 10000 ∧ 1 ≤ m ∧ m ≤ 10000 ∧ 1 ≤ k ∧ k ≤ 2 * n * m

def ValidOutput (n m : Int) (lane desk : Int) (side : String) : Prop :=
  1 ≤ lane ∧ lane ≤ n ∧ 1 ≤ desk ∧ desk ≤ m ∧ (side = "L" ∨ side = "R")

def CorrectSolution (n m k lane desk : Int) (side : String) : Prop :=
  lane = (k - 1) / (2 * m) + 1 ∧
  desk = (k - 1) % (2 * m) / 2 + 1 ∧
  (side = "L" ↔ (k - 1) % (2 * m) % 2 = 0)

@[reducible, simp]
def solve_precond (n m k : Int) : Prop :=
  ValidInput n m k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Int) (h_precond : solve_precond n m k) : Int × Int × String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (result : Int × Int × String) (h_precond : solve_precond n m k) : Prop :=
  ValidOutput n m result.1 result.2.1 result.2.2 ∧
  CorrectSolution n m k result.1 result.2.1 result.2.2

theorem solve_spec_satisfied (n m k : Int) (h_precond : solve_precond n m k) :
    solve_postcond n m k (solve n m k h_precond) h_precond := by
  sorry
-- </vc-theorems>