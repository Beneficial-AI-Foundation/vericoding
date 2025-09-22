-- <vc-preamble>
def ValidDay (day : String) : Prop :=
  day ∈ ["SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT"]

def DaysUntilSunday (day : String) : Int :=
  match day with
  | "SUN" => 7
  | "MON" => 6  
  | "TUE" => 5
  | "WED" => 4
  | "THU" => 3
  | "FRI" => 2
  | "SAT" => 1
  | _ => 0

@[reducible, simp]
def solve_precond (day : String) : Prop :=
  ValidDay day
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (day : String) (h_precond : solve_precond day) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (day : String) (result : Int) (h_precond : solve_precond day) : Prop :=
  result ≥ 1 ∧ result ≤ 7 ∧ result = DaysUntilSunday day

theorem solve_spec_satisfied (day : String) (h_precond : solve_precond day) :
    solve_postcond day (solve day h_precond) h_precond := by
  sorry
-- </vc-theorems>