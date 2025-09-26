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
@[simp] lemma ExpectedResult_self (s : String) : ExpectedResult s = ExpectedResult s := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (statuses : String) (h_precond : solve_precond n statuses) : Int :=
  ExpectedResult statuses
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (statuses : String) (result: Int) (h_precond : solve_precond n statuses) : Prop :=
  result = ExpectedResult statuses

theorem solve_spec_satisfied (n : Int) (statuses : String) (h_precond : solve_precond n statuses) :
    solve_postcond n statuses (solve n statuses h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
