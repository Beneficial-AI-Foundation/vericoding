-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def CanMakeSum (n l r : Int) : Bool :=
  l > 0 && l ≤ r && n > 0 && n % l ≤ (r - l) * (n / l)

def ValidOutput (result : String) : Prop :=
  result.length ≥ 0 ∧ ∀ i, 0 ≤ i ∧ i < result.length → True

def SplitLines (s : String) : List String := s.splitOn "\n"

def ParseInt (s : String) : Int := s.toInt?.getD 0

def SplitSpaces (s : String) : List String := s.splitOn " "

def CorrectSolution (input result : String) : Prop :=
  let lines := SplitLines input
  lines.length > 0 → 
  (let t := ParseInt (lines.head!)
   let outputLines := SplitLines result
   outputLines.length ≥ 1 ∧ (outputLines.length = 1 → outputLines.head! = "") ∧
   (outputLines.length > 1 → outputLines.getLast! = "") ∧
   ∀ i, 1 ≤ i ∧ i ≤ t ∧ Int.natAbs i < lines.length →
      (let parts := SplitSpaces (lines[Int.natAbs i]!)
       parts.length ≥ 3 →
       (let n := ParseInt (parts.head!)
        let l := ParseInt (parts[1]!)
        let r := ParseInt (parts[2]!)
        let expectedOutput := if CanMakeSum n l r then "Yes" else "No"
        Int.natAbs (i - 1) < outputLines.length ∧ outputLines[Int.natAbs (i - 1)]! = expectedOutput)))

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result ∧ CorrectSolution input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>