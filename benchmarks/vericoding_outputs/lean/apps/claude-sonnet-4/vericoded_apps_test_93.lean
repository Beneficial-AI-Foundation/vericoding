import Mathlib
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
-- LLM HELPER: Check if puzzles can reach same config (simplified since rotatePuzzleLeft ignores rotation)
def canReachSameConfigDecision (input : String) : Bool :=
  extractAndNormalizePuzzle1 input = extractAndNormalizePuzzle2 input

-- LLM HELPER: Decidable instance for CanReachSameConfig
instance (input : String) : Decidable (CanReachSameConfig input) :=
  if h : canReachSameConfigDecision input then
    isTrue (by
      use 0
      constructor
      · norm_num
      constructor  
      · norm_num
      · unfold canReachSameConfigDecision at h
        simp [rotatePuzzleLeft]
        exact decide_eq_true_iff.mp h
    )
  else
    isFalse (by
      intro ⟨rotation, h_ge, h_lt, h_eq⟩
      unfold canReachSameConfigDecision at h
      simp [rotatePuzzleLeft] at h_eq
      have h_false : decide (extractAndNormalizePuzzle1 input = extractAndNormalizePuzzle2 input) = false := by
        rw [decide_eq_false_iff_not]
        rw [decide_eq_true_iff] at h
        exact h
      have : ¬(extractAndNormalizePuzzle1 input = extractAndNormalizePuzzle2 input) := decide_eq_false_iff_not.mp h_false
      exact this h_eq
    )
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  if CanReachSameConfig input then "YES\n" else "NO\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (result = "YES\n" ∨ result = "NO\n") ∧ 
  (result = "YES\n" ↔ CanReachSameConfig input)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · -- First part: result is either "YES\n" or "NO\n"
    by_cases h : CanReachSameConfig input
    · simp [h]
    · simp [h]
  · -- Second part: result = "YES\n" iff CanReachSameConfig input
    by_cases h : CanReachSameConfig input
    · simp [h]
    · simp [h]
-- </vc-theorems>
