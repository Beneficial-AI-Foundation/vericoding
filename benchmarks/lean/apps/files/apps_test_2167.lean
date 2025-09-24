-- <vc-preamble>
def ValidInput (n : Int) (arr : List Int) : Prop :=
  n ≥ 1 ∧ arr.length = n

def sum_seq (s : List Int) : Int :=
  s.sum

def CorrectResult (n : Int) (arr : List Int) (result : Int) : Prop :=
  ValidInput n arr →
  (sum_seq arr % n = 0 → result = n) ∧
  (sum_seq arr % n ≠ 0 → result = n - 1) ∧
  (result = n ∨ result = n - 1)

@[reducible, simp]
def solve_precond (n : Int) (arr : List Int) : Prop :=
  ValidInput n arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (arr : List Int) (h_precond : solve_precond n arr) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (arr : List Int) (result : Int) (h_precond : solve_precond n arr) : Prop :=
  CorrectResult n arr result

theorem solve_spec_satisfied (n : Int) (arr : List Int) (h_precond : solve_precond n arr) :
    solve_postcond n arr (solve n arr h_precond) h_precond := by
  sorry
-- </vc-theorems>