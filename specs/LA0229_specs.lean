-- <vc-preamble>
partial def CountOnesInOctal (a : Int) : Int :=
  if a = 0 then 0
  else (if a % 8 = 1 then 1 else 0) + CountOnesInOctal (a / 8)

@[reducible, simp]
def solve_precond (a : Int) : Prop :=
  a ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : Int) (h_precond : solve_precond a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : Int) (count : Int) (h_precond : solve_precond a) : Prop :=
  count ≥ 0 ∧ count = CountOnesInOctal a

theorem solve_spec_satisfied (a : Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>