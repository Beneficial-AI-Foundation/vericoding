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
def parse_line_nums (line : String) : Int × Int := 
  let parts := SplitBySpace line
  (StringToIntVal (parts[0]!), StringToIntVal (parts[1]!))

-- LLM HELPER
def generate_cyclic_pattern (n k : Int) : String := 
  let n_nat := n.natAbs
  let k_nat := k.natAbs
  let chars := List.range n_nat |>.map (fun j => 
    Char.ofNat ((j % k_nat) + 97)
  )
  String.mk chars
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let lines := SplitByNewline stdin_input
  let T := (StringToIntVal (lines[0]!)).natAbs
  let test_case_lines := lines.drop 1
  let relevant_lines := test_case_lines.take T

  let results := relevant_lines.map fun line =>
    let (n, k) := parse_line_nums line
    generate_cyclic_pattern n k

  String.intercalate "\n" results
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length ≥ 0

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  simp
-- </vc-theorems>
