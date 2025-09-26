-- <vc-preamble>
-- Helper functions for string processing (axiomatized for now)
axiom SplitLines : String → List String
axiom SplitByChar : String → Char → List String
axiom ParseLine : String → List Int

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧ (∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9')

def ValidPlayerLine (line : String) : Prop :=
  let parts := SplitByChar line ' '
  parts.length = 2 ∧
  IsValidInteger parts[0]! ∧
  IsValidInteger parts[1]!

def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 4 ∧ 
  (∀ i, 0 ≤ i ∧ i < 4 → ValidPlayerLine lines[i]!)

noncomputable def ComputeResult (input : String) : String :=
  let lines := SplitLines input
  if lines.length < 4 then ""
  else
    let player1 := ParseLine lines[0]!
    let player2 := ParseLine lines[1]!
    let player3 := ParseLine lines[2]!
    let player4 := ParseLine lines[3]!
    
    if player1.length ≠ 2 ∨ player2.length ≠ 2 ∨ player3.length ≠ 2 ∨ player4.length ≠ 2 then ""
    else
      let a := player1[0]!
      let b := player1[1]!
      let c := player2[0]!
      let d := player2[1]!
      let x := player3[0]!
      let y := player3[1]!
      let z := player4[0]!
      let w := player4[1]!
      
      let Team1 := (a > w ∧ a > y ∧ d > x ∧ d > z) ∨ (c > w ∧ c > y ∧ b > x ∧ b > z)
      let Team2 := ((x > b ∧ w > c) ∨ (z > b ∧ y > c)) ∧ ((x > d ∧ w > a) ∨ (z > d ∧ y > a))
      
      if Team1 then "Team 1\n"
      else if Team2 then "Team 2\n"
      else "Draw\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = ComputeResult input ∧
  (result = "Team 1\n" ∨ result = "Team 2\n" ∨ result = "Draw\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>