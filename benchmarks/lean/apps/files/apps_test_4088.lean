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
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
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
  sorry
-- </vc-theorems>