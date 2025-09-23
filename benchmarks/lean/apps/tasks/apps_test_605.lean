-- <vc-preamble>
def ValidInput (a b c d : Int) : Prop :=
  250 ≤ a ∧ a ≤ 3500 ∧ a % 250 = 0 ∧
  250 ≤ b ∧ b ≤ 3500 ∧ b % 250 = 0 ∧
  0 ≤ c ∧ c ≤ 180 ∧
  0 ≤ d ∧ d ≤ 180

def CalculateScore (points time : Int) : Float :=
  let min_score := 3.0 * (Float.ofInt points) / 10.0
  let time_adjusted := (Float.ofInt points) - (Float.ofInt points) * (Float.ofInt time) / 250.0
  if min_score ≥ time_adjusted then min_score else time_adjusted

def CorrectResult (a b c d : Int) (result : String) (h : ValidInput a b c d) : Prop :=
  let misha_score := CalculateScore a c
  let vasya_score := CalculateScore b d
  (result = "Misha" ↔ misha_score > vasya_score) ∧
  (result = "Vasya" ↔ vasya_score > misha_score) ∧
  (result = "Tie" ↔ misha_score = vasya_score)

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  ValidInput a b c d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result : String) (h_precond : solve_precond a b c d) : Prop :=
  (result = "Misha" ∨ result = "Vasya" ∨ result = "Tie") ∧
  CorrectResult a b c d result h_precond

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  sorry
-- </vc-theorems>