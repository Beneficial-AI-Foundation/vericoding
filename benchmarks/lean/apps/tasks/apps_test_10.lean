-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def MinDaysOff (n : Int) (h : ValidInput n) : Int :=
  let completeWeeks := n / 7
  let remainingDays := n % 7
  let minAdditional := if remainingDays > 5 then remainingDays - 5 else 0
  2 * completeWeeks + minAdditional

def MaxDaysOff (n : Int) (h : ValidInput n) : Int :=
  let completeWeeks := n / 7
  let remainingDays := n % 7
  let maxAdditional := if remainingDays < 2 then remainingDays else 2
  2 * completeWeeks + maxAdditional

def ValidOutput (result : List Int) (n : Int) (h : ValidInput n) : Prop :=
  result.length = 2 ∧
  result[0]! ≥ 0 ∧ result[1]! ≥ 0 ∧
  result[0]! ≤ result[1]! ∧
  result[0]! ≤ n ∧ result[1]! ≤ n ∧
  result[0]! = MinDaysOff n h ∧
  result[1]! = MaxDaysOff n h

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List Int) (h_precond : solve_precond n) : Prop :=
  ValidOutput result n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>