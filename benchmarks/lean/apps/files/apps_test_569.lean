-- <vc-preamble>
def ValidInput (n : Int) (s : String) : Prop :=
  n = s.length ∧ n ≥ 1

def CountDistinctChars (s : String) : Nat :=
  s.toList.eraseDups.length

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : Int) (h_precond : solve_precond n s) : Prop :=
  (n > 26 → result = -1) ∧
  (n ≤ 26 → result ≥ 0 ∧ result < n) ∧
  (n ≤ 26 → result = s.length - (CountDistinctChars s : Int))

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>