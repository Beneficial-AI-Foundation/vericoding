-- <vc-preamble>
def countNewlines (s : String) : Int :=
  s.data.foldl (fun acc c => if c = '\n' then acc + 1 else acc) 0

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ '\n' ∈ input.data ∧ countNewlines input ≥ 3

def splitLines (input : String) : List String := 
  input.splitOn "\n"

def reverse (s : String) : String := 
  s.data.reverse.asString

def removeFirstX (s : String) : String := 
  if s.length > 0 ∧ s.get! 0 = 'X' then s.drop 1 else s

def rotatePuzzleLeft (s : String) (_ : Int) : String := 
  s

def extractAndNormalizePuzzle1 (input : String) : String :=
  let lines := splitLines input
  if lines.length ≥ 2 then
    let line1 := lines[0]!
    let line2 := reverse (lines[1]!)
    let combined := line1 ++ line2
    removeFirstX combined
  else
    ""

def extractAndNormalizePuzzle2 (input : String) : String :=
  let lines := splitLines input
  if lines.length ≥ 4 then
    let line3 := lines[2]!
    let line4 := reverse (lines[3]!)
    let combined := line3 ++ line4
    removeFirstX combined
  else
    ""

def CanReachSameConfig (input : String) : Prop :=
  ∃ rotation, 0 ≤ rotation ∧ rotation < 4 ∧ 
    extractAndNormalizePuzzle1 input = rotatePuzzleLeft (extractAndNormalizePuzzle2 input) rotation

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
  (result = "YES\n" ∨ result = "NO\n") ∧ 
  (result = "YES\n" ↔ CanReachSameConfig input)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>