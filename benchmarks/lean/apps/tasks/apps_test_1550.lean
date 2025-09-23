-- <vc-preamble>
def ValidInput (n : Int) (digits : String) : Bool :=
  n > 0 && digits.length = n.natAbs && (List.range digits.length).all (fun i => 
    let c := digits.data[i]!
    '0' ≤ c && c ≤ '9')

def transformDigits (s : String) (key : Int) : String :=
  s.data.foldl (fun acc c =>
    let digit := ((c).toNat - '0'.toNat + key.natAbs) % 10
    acc ++ String.mk [Char.ofNat ('0'.toNat + digit)]) ""

def rotateString (s : String) (index : Int) : String :=
  if s.length = 0 then ""
  else if 0 ≤ index ∧ index < s.length then
    s.drop index.natAbs ++ s.take index.natAbs
  else s

def modifyString (s : String) (index : Int) : String :=
  if 0 ≤ index ∧ index < s.length then
    let key := if s.data[index.natAbs]! = '0' then 0 else 10 - ((s.data[index.natAbs]!).toNat - '0'.toNat)
    let transformed := transformDigits s key
    rotateString transformed index
  else s

def isAllDigits (s : String) : Bool :=
  (List.range s.length).all (fun i =>
    let c := s.data[i]!
    '0' ≤ c && c ≤ '9')

def parseInputHelper (input : String) (i : Nat) (currentLine : String) (lines : List String) : List String :=
  if i ≥ input.length then
    if currentLine.length > 0 then lines ++ [currentLine] else lines
  else if input.data[i]! = '\n' then
    parseInputHelper input (i + 1) "" (lines ++ [currentLine])
  else
    parseInputHelper input (i + 1) (currentLine ++ String.mk [input.data[i]!]) lines
  termination_by (input.length - i)

def parseInput (input : String) : List String :=
  parseInputHelper input 0 "" []

def parseInt (s : String) : Int :=
  s.data.foldl (fun acc c =>
    if '0' ≤ c ∧ c ≤ '9' then
      acc * 10 + Int.ofNat (c.toNat - '0'.toNat)
    else acc) 0

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ∃ i, 0 ≤ i ∧ i < stdin_input.length ∧ stdin_input.data[i]! = '\n'
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
  result.length > 0 ∧ 
  result.data[result.length - 1]! = '\n' ∧
  (let lines := parseInput stdin_input
   if lines.length ≥ 2 then
     let n := parseInt lines[0]!
     let digits := lines[1]!
     if ValidInput n digits then
       let minResult := result.take (result.length - 1)
       minResult.length = n.natAbs ∧
       isAllDigits minResult ∧
       (∃ index, 0 ≤ index ∧ index < n ∧ minResult = modifyString digits index) ∧
       (∀ index, 0 ≤ index ∧ index < n → minResult ≤ modifyString digits index)
     else
       result = "\n"
   else
     result = "\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>