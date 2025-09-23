-- <vc-preamble>
def SplitLines (s : String) : List String := 
  s.splitOn "\n"

def StringToInt (s : String) : Int := 
  s.toInt?.getD 0

def IndexOf (s : String) (c : Char) : Int := 
  let chars := s.toList
  let rec findChar (lst : List Char) (idx : Nat) : Int :=
    match lst with
    | [] => -1
    | h :: t => if h = c then idx else findChar t (idx + 1)
  findChar chars 0

def IndexOfFrom (s : String) (c : Char) (start : Int) : Int := 
  let chars := s.toList
  let rec findFrom (lst : List Char) (idx : Nat) : Int :=
    match lst with
    | [] => -1
    | h :: t => if idx ≥ start.natAbs && h = c then idx else findFrom t (idx + 1)
  findFrom chars 0

def Reverse (s : String) : String := 
  String.mk s.toList.reverse

def IsBinaryString (s : String) : Prop :=
  s.length > 0 ∧ (∀ c ∈ s.toList, c = '0' ∨ c = '1')

def ContainsOne (s : String) : Prop :=
  '1' ∈ s.toList

def IsValidNumber (s : String) : Prop :=
  s.length > 0 ∧ (∀ c ∈ s.toList, '0' ≤ c ∧ c ≤ '9')

def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 1 ∧ 
  IsValidNumber (lines[0]!) ∧
  (let T := StringToInt (lines[0]!)
   T ≥ 0 ∧ Int.ofNat lines.length ≥ 2 * T + 1 ∧
   (∀ i : Int, 1 ≤ i ∧ i < 2 * T + 1 → i.natAbs < lines.length ∧ IsBinaryString (lines[i.natAbs]!) ∧ ContainsOne (lines[i.natAbs]!)))

def ValidOutput (output : String) (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 1 →
  let T := StringToInt (lines[0]!)
  let outputLines := if output = "" then [] else SplitLines output
  Int.ofNat outputLines.length = T ∧
  (∀ i : Int, 0 ≤ i ∧ i < T → IsValidNumber (outputLines[i.natAbs]!))

def CorrectComputation (output : String) (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 1 →
  let T := StringToInt (lines[0]!)
  let outputLines := if output = "" then [] else SplitLines output
  Int.ofNat outputLines.length = T ∧
  (∀ i : Int, 0 ≤ i ∧ i < T ∧ 1 + 2*i < Int.ofNat lines.length ∧ 2 + 2*i < Int.ofNat lines.length → 
      let x := lines[(1 + 2*i).natAbs]!
      let y := lines[(2 + 2*i).natAbs]!
      let revX := Reverse x
      let revY := Reverse y
      let start := IndexOf revY '1'
      start ≥ 0 ∧
      let offset := IndexOfFrom revX '1' start
      StringToInt (outputLines[i.natAbs]!) = offset)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ 
  input.toList[input.length - 1]! = '\n' ∧ 
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
  ValidOutput result input ∧ 
  (result.length > 0 → result.toList[result.length - 1]! ≠ '\n') ∧ 
  CorrectComputation result input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>