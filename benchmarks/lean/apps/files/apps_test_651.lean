-- <vc-preamble>
def SplitLines (_ : String) : List String := []

def ParseTwoInts (_ : String) : Int × Int := (0, 0)

def CountOccurrences (_ : List String) (_ _ : Int) (_ : Char) : Int := 0

def FindStart (_ : List String) (_ _ : Int) : Int × Int := (0, 0)

def FindEnd (_ : List String) (_ _ : Int) : Int × Int := (0, 0)

def CountPermutationsReachingGoal (_ : List String) (_ _ : Int) (_ : String) (_ _ : Int × Int) : Int := 0

def StringToInt (_ : String) : Int := 0

def ValidPathString (path : String) : Prop :=
  ∀ i : Nat, i < path.length → '0' ≤ path.data[i]! ∧ path.data[i]! ≤ '3'

def HasValidDimensions (lines : List String) : Prop :=
  if lines.length ≥ 1 then
    let dimensions := ParseTwoInts lines[0]!
    let n := dimensions.1
    let m := dimensions.2
    n > 0 ∧ m > 0 ∧ lines.length ≥ Int.natAbs (n + 2)
  else
    False

def HasValidGrid (lines : List String) : Prop :=
  if lines.length ≥ 1 then
    let dimensions := ParseTwoInts lines[0]!
    let n := dimensions.1
    let m := dimensions.2
    n > 0 ∧ m > 0 ∧ lines.length ≥ Int.natAbs (n + 2) ∧
    ∀ i : Nat, 1 ≤ i ∧ i ≤ Int.natAbs n ∧ i < lines.length →
      ∀ j : Nat, j < lines[i]!.length ∧ j < Int.natAbs m →
        lines[i]!.data[j]! ∈ ['.', '#', 'S', 'E']
  else
    False

def HasStartAndEnd (lines : List String) : Prop :=
  if lines.length ≥ 1 then
    let dimensions := ParseTwoInts lines[0]!
    let n := dimensions.1
    let m := dimensions.2
    n > 0 ∧ m > 0 ∧ lines.length ≥ Int.natAbs (n + 2) ∧
    (∃ i j : Nat, 1 ≤ i ∧ i ≤ Int.natAbs n ∧ i < lines.length ∧ j < lines[i]!.length ∧ j < Int.natAbs m ∧ lines[i]!.data[j]! = 'S') ∧
    (∃ i j : Nat, 1 ≤ i ∧ i ≤ Int.natAbs n ∧ i < lines.length ∧ j < lines[i]!.length ∧ j < Int.natAbs m ∧ lines[i]!.data[j]! = 'E') ∧
    CountOccurrences lines n m 'S' = 1 ∧
    CountOccurrences lines n m 'E' = 1
  else
    False

def HasValidPath (lines : List String) : Prop :=
  if lines.length ≥ 1 then
    let dimensions := ParseTwoInts lines[0]!
    let n := dimensions.1
    let m := dimensions.2
    n > 0 ∧ m > 0 ∧ lines.length ≥ Int.natAbs (n + 2) ∧
    ValidPathString lines[Int.natAbs (n + 1)]!
  else
    False

def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 3 ∧
  HasValidDimensions lines ∧
  HasValidGrid lines ∧
  HasStartAndEnd lines ∧
  HasValidPath lines

def ValidResult (result : String) : Prop :=
  result.length > 0 ∧
  ∀ c : Char, c ∈ result.data → ('0' ≤ c ∧ c ≤ '9') ∨ c = '\n'

def CountValidWays (_ : String) : Int := 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0
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
  ValidResult result ∧
  (let numResult := StringToInt (if '\n' ∈ result.data then result.take (result.length - 1) else result)
   0 ≤ numResult ∧ numResult ≤ 24) ∧
  (ValidInput stdin_input →
   let numResult := StringToInt (if '\n' ∈ result.data then result.take (result.length - 1) else result)
   numResult = CountValidWays stdin_input) ∧
  (¬ValidInput stdin_input →
   StringToInt (if '\n' ∈ result.data then result.take (result.length - 1) else result) = 0)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>