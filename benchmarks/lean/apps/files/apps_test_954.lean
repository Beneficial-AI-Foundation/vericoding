-- <vc-preamble>
def CyclicShiftForward (s : String) : String :=
  if s.length > 0 then
    s.drop 1 ++ s.take 1
  else
    s

def ValidInput (s : String) : Prop :=
  s.length > 0

def ApplyShifts (s : String) (steps : Nat) : String :=
  match steps with
  | 0 => s
  | n + 1 => CyclicShiftForward (ApplyShifts s n)

def AllDistinctCyclicShifts (s : String) : List String :=
  List.range s.length |>.map (fun i => ApplyShifts s i)

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  1 ≤ result ∧ result ≤ s.length ∧ result = (AllDistinctCyclicShifts s).eraseDups.length

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>