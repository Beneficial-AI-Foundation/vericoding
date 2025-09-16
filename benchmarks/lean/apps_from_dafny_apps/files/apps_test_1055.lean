-- <vc-preamble>
-- <vc-preamble>
def ValidInput (a : List Int) : Prop :=
  a.length > 0

def isSorted (x : List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < x.length → x[i]! ≤ x[j]!

def thanosSort (x : List Int) : Int := sorry

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  ValidInput a
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : Int) (h_precond : solve_precond a) : Prop :=
  result = thanosSort a ∧ 1 ≤ result ∧ result ≤ a.length

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
