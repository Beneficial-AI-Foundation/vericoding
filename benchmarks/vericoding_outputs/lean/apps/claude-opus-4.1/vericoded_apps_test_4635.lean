import Mathlib
-- <vc-preamble>
def SplitByNewline (s : String) : List String := s.splitOn "\n"

def SplitBySpace (s : String) : List String := s.splitOn " "

def IsValidInteger (s : String) : Bool := 
  s.length > 0 && 
  (s.length == 1 || s.data[0]! != '0' || s == "0") &&
  s.data.all (fun c => '0' ≤ c && c ≤ '9')

def StringToIntVal (s : String) : Int := 
  s.data.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

def ValidTestCaseLine (line : String) : Bool :=
  let parts := SplitBySpace line
  parts.length ≥ 2 &&
  IsValidInteger (parts[0]!) &&
  IsValidInteger (parts[1]!) &&
  StringToIntVal (parts[0]!) > 0 &&
  StringToIntVal (parts[1]!) > 0 &&
  StringToIntVal (parts[1]!) ≤ 26

def ValidInput (input : String) : Bool :=
  input.length > 0 && 
  let lines := SplitByNewline input
  lines.length ≥ 1 && 
  IsValidInteger (lines[0]!) &&
  StringToIntVal (lines[0]!) ≥ 0 &&
  lines.length ≥ (StringToIntVal (lines[0]!)).natAbs + 1 &&
  (List.range (StringToIntVal (lines[0]!)).natAbs).all (fun i => 
    i + 1 < lines.length && ValidTestCaseLine (lines[i + 1]!))

def CyclicPatternCorrect (n k : Int) (output : String) : Bool :=
  n > 0 && k > 0 && k ≤ 26 &&
  output.length = n.natAbs &&
  (List.range n.natAbs).all (fun j => 
    output.data[j]! = Char.ofNat ((j % k.natAbs) + 97))

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input = true
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def GenerateCyclicPattern (n k : Int) : String :=
  String.mk (List.map (fun j => Char.ofNat ((j % k.natAbs) + 97)) (List.range n.natAbs))

-- LLM HELPER
def ProcessTestCase (line : String) : String :=
  let parts := SplitBySpace line
  if parts.length ≥ 2 then
    let n := StringToIntVal (parts[0]!)
    let k := StringToIntVal (parts[1]!)
    GenerateCyclicPattern n k
  else
    ""

-- LLM HELPER
def ProcessAllTestCases (lines : List String) (start : Nat) (count : Nat) : String :=
  match count with
  | 0 => ""
  | n + 1 => 
    if start < lines.length then
      ProcessTestCase (lines[start]!) ++ "\n" ++ ProcessAllTestCases lines (start + 1) n
    else
      ""
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let lines := SplitByNewline stdin_input
  let t := StringToIntVal (lines[0]!)
  let output := ProcessAllTestCases lines 1 t.natAbs
  if output.length > 0 && output.data[output.length - 1]! = '\n' then
    output.dropRight 1
  else
    output
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length ≥ 0

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond
  simp
-- </vc-theorems>
