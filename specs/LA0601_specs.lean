-- <vc-preamble>
def ValidInput (d : Int) : Prop :=
  22 ≤ d ∧ d ≤ 25

def RepeatEve (count : Nat) : String :=
  match count with
  | 0 => ""
  | n + 1 => " Eve" ++ RepeatEve n

def ExpectedOutput (d : Int) : String :=
  let eveCount := (25 - d).natAbs
  let baseString := "Christmas"
  if eveCount = 0 then baseString
  else baseString ++ RepeatEve eveCount

@[reducible, simp]
def solve_precond (d : Int) : Prop :=
  ValidInput d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (d : Int) (h_precond : solve_precond d) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (d : Int) (result : String) (h_precond : solve_precond d) : Prop :=
  result = ExpectedOutput d

theorem solve_spec_satisfied (d : Int) (h_precond : solve_precond d) :
    solve_postcond d (solve d h_precond) h_precond := by
  sorry
-- </vc-theorems>