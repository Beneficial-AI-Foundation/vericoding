-- <vc-preamble>

def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 2000000000

def ValidOutput (n : Int) (result : Int) : Prop :=
  result ≥ 0 ∧
  result ≥ n - 1 ∧
  result ≤ n * (n - 1) / 2

def isqrt (n : Int) : Int :=
  if n ≤ 0 then 0
  else if n = 1 then 1
  else if n ≤ 3 then 1
  else
    let approx := n / 2
    max 0 approx

def ComputeExpectedResult (n : Int) : Int :=
  let quad_solv_numerator := isqrt (8*n + 1) - 1
  let x := quad_solv_numerator / 2
  let y := x + 1
  let xed := x * (x - 1) / 2 + n - x
  let ybr := n - y
  let yed := 2 * ybr
  if xed > yed then xed else yed

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
  ValidOutput n result ∧ result = ComputeExpectedResult n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>