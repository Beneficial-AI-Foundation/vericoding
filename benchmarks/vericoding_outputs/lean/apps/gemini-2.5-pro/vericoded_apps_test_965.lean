import Mathlib
-- <vc-preamble>

def ValidInput (n: Int) (statuses: String) : Prop :=
  n ≥ 2 ∧ statuses.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < statuses.length → statuses.get (String.Pos.mk i) ∈ ['A', 'I', 'F']

def CountStatus (statuses: String) (status: Char) : Int :=
  (List.range statuses.length).filter (fun i => statuses.get (String.Pos.mk i) = status) |>.length

def ExpectedResult (statuses: String) : Int :=
  let cnt_I := CountStatus statuses 'I'
  let cnt_A := CountStatus statuses 'A'
  if cnt_I = 0 then cnt_A
  else if cnt_I = 1 then 1
  else 0

@[reducible, simp]
def solve_precond (n : Int) (statuses : String) : Prop :=
  ValidInput n statuses
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
/-- The number of occurrences of a status is always non-negative. -/
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (statuses : String) (h_precond : solve_precond n statuses) : Int :=
  let cnt_I := CountStatus statuses 'I'
  match cnt_I with
  | 0 => CountStatus statuses 'A'
  | 1 => 1
  | _ => 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (statuses : String) (result: Int) (h_precond : solve_precond n statuses) : Prop :=
  result = ExpectedResult statuses

theorem solve_spec_satisfied (n : Int) (statuses : String) (h_precond : solve_precond n statuses) :
    solve_postcond n statuses (solve n statuses h_precond) h_precond := by
  unfold solve_postcond ExpectedResult solve
  -- After unfolding, the goal is to show that the `match` expression in `solve` is
  -- equivalent to the `if-then-else` expression in `ExpectedResult`.
  -- `simp` will simplify the `let` expressions inside `ExpectedResult`.
  simp

  -- `split_ifs` will perform a case analysis on the conditions of the `if-then-else`
  -- expression from `ExpectedResult`.
  split_ifs with h_cnt_I_eq_0 h_cnt_I_eq_1

  -- For each case, `simp_all` uses the generated hypotheses (e.g., `h_cnt_I_eq_0`)
  -- to simplify both sides of the equality, which become equal.
  · simp_all
  · simp_all
  · simp_all
-- </vc-theorems>
