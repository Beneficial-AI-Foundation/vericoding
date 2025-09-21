-- <vc-preamble>
def DistinctStrings (strings : List String) : Nat :=
  (strings.eraseDups).length

def ValidInput (strings : List String) : Prop :=
  strings.length ≥ 1

@[reducible, simp]
def solve_precond (strings : List String) : Prop :=
  ValidInput strings
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (strings : List String) (h_precond : solve_precond strings) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (strings : List String) (count : Int) (h_precond : solve_precond strings) : Prop :=
  count ≥ 1 ∧ count ≤ strings.length ∧ count = DistinctStrings strings

theorem solve_spec_satisfied (strings : List String) (h_precond : solve_precond strings) :
    solve_postcond strings (solve strings h_precond) h_precond := by
  sorry
-- </vc-theorems>