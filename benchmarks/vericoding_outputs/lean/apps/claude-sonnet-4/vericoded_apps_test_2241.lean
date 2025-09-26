import Mathlib
-- <vc-preamble>
def sum_contributions (a b : List Int) : Int :=
  match a, b with
  | [], [] => 0
  | a_head :: a_tail, b_head :: b_tail =>
      (if b_head > 1 ∧ 2 * a_head ≥ b_head then
          let x := b_head / 2
          let y := b_head - x
          x * y
       else -1) + sum_contributions a_tail b_tail
  | _, _ => 0

@[reducible, simp]
def solve_precond (a b : List Int) : Prop :=
  a.length = b.length
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (a b : List Int) (h_precond : solve_precond a b) : Int :=
  sum_contributions a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : List Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result = sum_contributions a b

theorem solve_spec_satisfied (a b : List Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve; rfl
-- </vc-theorems>
