-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidOutput (result : String) : Prop :=
  result = "Kuro" ∨ result = "Shiro" ∨ result = "Katie" ∨ result = "Draw" ∨ result = ""

-- Placeholder function declarations that would need implementation
noncomputable axiom MaxCharFreq : String → Int
noncomputable axiom SplitLines : String → List String
noncomputable axiom ParseInt : String → Int
noncomputable axiom Max3 : Int → Int → Int → Int

noncomputable def OptimalScore (ribbon : String) (turns : Int) : Int :=
  let maxFreq := MaxCharFreq ribbon
  let length := ribbon.length
  if turns = 1 ∧ maxFreq = length then 
    if maxFreq > 0 then maxFreq - 1 else 0
  else if length < maxFreq + turns then length
  else maxFreq + turns

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
noncomputable def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result ∧
  (let lines := SplitLines input
   if lines.length < 4 then result = ""
   else (
     let turns := ParseInt (lines[0]!)
     let s0 := lines[1]!
     let s1 := lines[2]!
     let s2 := lines[3]!
     let score0 := OptimalScore s0 turns
     let score1 := OptimalScore s1 turns
     let score2 := OptimalScore s2 turns
     let maxScore := Max3 score0 score1 score2
     let winners := (if score0 = maxScore then 1 else 0) + (if score1 = maxScore then 1 else 0) + (if score2 = maxScore then 1 else 0)
     (winners > 1 → result = "Draw") ∧
     (winners = 1 ∧ score0 = maxScore → result = "Kuro") ∧
     (winners = 1 ∧ score1 = maxScore → result = "Shiro") ∧
     (winners = 1 ∧ score2 = maxScore → result = "Katie")
   ))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>