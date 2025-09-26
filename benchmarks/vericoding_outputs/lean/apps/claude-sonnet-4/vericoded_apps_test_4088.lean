import Mathlib
-- <vc-preamble>
def SplitLines (_ : String) : List String := []

def IsValidInteger (_ : String) : Bool := true

def StringToInt (_ : String) : Int := 0

def IsValidString (_ : String) : Bool := true

def IsValidIntegerArray (_ : String) : Bool := true

def ParseIntegerArray (_ : String) : Array Int := #[]

def GetTestCases (_ : String) : List (String × Int × Array Int) := []

def CountChar (_ : String) (_ : Char) : Int := 0

def SumDistancesToGreaterCharsHelper (_ : String) (_ : Int) (_ : Int) : Int := 0

def SumDistancesToGreaterChars (t : String) (j : Int) : Int :=
  SumDistancesToGreaterCharsHelper t j 0

def AbsDiff (i j : Int) : Int :=
  if i ≥ j then i - j else j - i

def ValidInputFormat (input : String) : Prop := True

def ValidOutputFormat (output input : String) : Prop := True

def OutputSatisfiesConstraints (output input : String) : Prop := True

def PreservesCharacterUsage (output input : String) : Prop := True

def ContainsNewlineTerminatedResults (output : String) : Prop := True

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInputFormat stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Additional utility functions for string processing and formatting
def FormatResult (result : Int) : String := toString result ++ "\n"

def ProcessTestCase (testCase : String × Int × Array Int) : String :=
  let (s, j, _) := testCase
  let result := SumDistancesToGreaterChars s j
  FormatResult result

def ProcessAllTestCases (testCases : List (String × Int × Array Int)) : String :=
  testCases.foldl (fun acc tc => acc ++ ProcessTestCase tc) ""

-- LLM HELPER: Basic validation that input is non-empty
def ValidInput (input : String) : Bool := input.length > 0

-- LLM HELPER: Lemma about ProcessAllTestCases producing newline-terminated results
lemma ProcessAllTestCases_has_newlines (testCases : List (String × Int × Array Int)) :
    testCases ≠ [] → ContainsNewlineTerminatedResults (ProcessAllTestCases testCases) := by
  intro h_nonempty
  -- Since each ProcessTestCase produces a result with "\n", the overall result has newlines
  trivial
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  -- LLM HELPER: Main solve implementation
  let testCases := GetTestCases stdin_input
  ProcessAllTestCases testCases
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  ValidOutputFormat result stdin_input ∧
  OutputSatisfiesConstraints result stdin_input ∧
  PreservesCharacterUsage result stdin_input ∧
  (result ≠ "" → ContainsNewlineTerminatedResults result)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  -- LLM HELPER: Prove postcondition is satisfied
  unfold solve_postcond
  unfold solve
  simp
  constructor
  · -- ValidOutputFormat
    trivial
  constructor  
  · -- OutputSatisfiesConstraints
    trivial
  constructor
  · -- PreservesCharacterUsage 
    trivial
  · -- ContainsNewlineTerminatedResults
    intro h_nonempty
    -- We need to show ContainsNewlineTerminatedResults (ProcessAllTestCases (GetTestCases stdin_input))
    -- Since our ProcessTestCase always adds "\n", this is satisfied
    trivial
-- </vc-theorems>
