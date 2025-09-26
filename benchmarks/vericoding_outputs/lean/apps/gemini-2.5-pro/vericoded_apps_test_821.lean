import Mathlib
-- <vc-preamble>
def ValidInput (s v1 v2 t1 t2 : Int) : Prop :=
  1 ≤ s ∧ s ≤ 1000 ∧ 1 ≤ v1 ∧ v1 ≤ 1000 ∧ 1 ≤ v2 ∧ v2 ≤ 1000 ∧ 1 ≤ t1 ∧ t1 ≤ 1000 ∧ 1 ≤ t2 ∧ t2 ≤ 1000

def ParticipantTime (s v t : Int) : Int :=
  2 * t + s * v

def CorrectResult (s v1 v2 t1 t2 : Int) : String :=
  let time1 := ParticipantTime s v1 t1
  let time2 := ParticipantTime s v2 t2
  if time1 < time2 then "First"
  else if time1 > time2 then "Second"
  else "Friendship"

def ValidResult (result : String) : Prop :=
  result = "First" ∨ result = "Second" ∨ result = "Friendship"

@[reducible, simp]
def solve_precond (s v1 v2 t1 t2 : Int) : Prop :=
  ValidInput s v1 v2 t1 t2
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (s v1 v2 t1 t2 : Int) (h_precond : solve_precond s v1 v2 t1 t2) : String :=
  CorrectResult s v1 v2 t1 t2
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s v1 v2 t1 t2 : Int) (result : String) (h_precond : solve_precond s v1 v2 t1 t2) : Prop :=
  ValidResult result ∧ result = CorrectResult s v1 v2 t1 t2

theorem solve_spec_satisfied (s v1 v2 t1 t2 : Int) (h_precond : solve_precond s v1 v2 t1 t2) :
    solve_postcond s v1 v2 t1 t2 (solve s v1 v2 t1 t2 h_precond) h_precond := by
  simp [solve, solve_postcond, CorrectResult, ParticipantTime]
  unfold ValidResult
  split_ifs <;> simp
-- </vc-theorems>
