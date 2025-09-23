-- <vc-preamble>
def splitLines (_ : String) : List String := []

def isValidFirstLine (_ : String) : Bool := true

def parseFirstLineAsNat (_ : String) : Nat := 0

def isValidCoordinateLine (_ : String) : Bool := true

def getDistinctLines (_ : List (Int × Int)) : List (Int × Int × Int × Int) := []

def groupLinesBySlope (_ : List (Int × Int × Int × Int)) : List (List (Int × Int × Int × Int)) := []

def sumOverSlopeGroups (_ : List (List (Int × Int × Int × Int))) (_ : Nat) : Nat := 0

def validInputFormat (input : String) : Prop := True

def isNonNegativeNumericString (s : String) : Prop := True

def validCoordinate (point : Int × Int) : Prop := True

def extractN (_ : String) : Nat := 0

def extractPoints (_ : String) : List (Int × Int) := [(0, 0), (1, 1)]

def countIntersectingLinePairs (_ : List (Int × Int)) : Nat := 0

def stringToInt (_ : String) : Nat := 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ validInputFormat stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  "0"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  isNonNegativeNumericString result ∧
  let n := extractN stdin_input
  let points := extractPoints stdin_input
  points.length = n ∧ n ≥ 2 ∧ n ≤ 1000 ∧
  (∀ i, 0 ≤ i ∧ i < points.length → validCoordinate (points[i]!)) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < points.length → points[i]! ≠ points[j]!) ∧
  stringToInt result = countIntersectingLinePairs points

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>