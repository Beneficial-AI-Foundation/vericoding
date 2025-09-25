-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def vasya_eats_with_strategy (n : Int) (k : Int) : Int :=
  if n ≤ 0 then 0
  else
    let cur := if n < k then n else k
    let remaining_after_vasya := n - cur
    let remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10
    cur + vasya_eats_with_strategy remaining_after_petya k
termination_by n
decreasing_by
  simp_wf
  sorry

def IsMinimalSolution (n : Int) (k : Int) : Prop :=
  vasya_eats_with_strategy n k * 2 ≥ n ∧
  (k = 1 ∨ vasya_eats_with_strategy n (k - 1) * 2 < n)

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  1 ≤ result ∧ result ≤ n ∧ IsMinimalSolution n result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>