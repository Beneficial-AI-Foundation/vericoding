-- <vc-preamble>
def ValidInput (n : Int) (s : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ n ≤ 3000 ∧
  s ≥ 1 ∧ s ≤ 3000 ∧
  a.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < n → (a[i.natAbs]? ≠ none) ∧ a[i.natAbs]! ≥ 1 ∧ a[i.natAbs]! ≤ 3000

def ComputeDPTable (n : Int) (s : Int) (a : List Int) : List (List Int) :=
  sorry

def ComputeSubsetSumWays (n : Int) (s : Int) (a : List Int) : Int :=
  let dp := ComputeDPTable n s a
  if dp.length > n.natAbs ∧ (dp[n.natAbs]? ≠ none) ∧ dp[n.natAbs]!.length > s.natAbs then 
    if let some row := dp[n.natAbs]? then
      if let some val := row[s.natAbs]? then val else 0
    else 0
  else 0

def SplitLines (_ : String) : List String :=
  ["", ""]

def SplitWhitespace (_ : String) : List String :=
  [""]

def StringToInt (_ : String) : Int :=
  0

def IntToString (_ : Int) : String :=
  "0"

def ValidParsedInput (input : String) (n : Int) (s : Int) (a : List Int) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 2 ∧
  (let first_line := SplitWhitespace (lines[0]!)
   let second_line := SplitWhitespace (lines[1]!)
   first_line.length ≥ 2 ∧ second_line.length = n.natAbs ∧
   n = StringToInt (first_line[0]!) ∧
   s = StringToInt (first_line[1]!) ∧
   a.length = n.natAbs ∧
   (∀ i, 0 ≤ i ∧ i < n → a[i.natAbs]! = StringToInt (second_line[i.natAbs]!)) ∧
   ValidInput n s a)

def ValidParsedInputExists (input : String) : Bool :=
  let lines := SplitLines input
  if lines.length < 2 then false
  else
    let first_line := SplitWhitespace (lines[0]!)
    let second_line := SplitWhitespace (lines[1]!)
    if first_line.length < 2 ∨ second_line.length = 0 then false
    else
      let n := StringToInt (first_line[0]!)
      let s_val := StringToInt (first_line[1]!)
      n ≥ 1 && n ≤ 3000 && s_val ≥ 1 && s_val ≤ 3000 && second_line.length = n.natAbs &&
      true

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
  result.length > 0 ∧
  (result.length > 0 → result.data[result.length - 1]! = '\n') ∧
  (if ValidParsedInputExists stdin_input then
    ∃ n s a, 
      ValidParsedInput stdin_input n s a ∧
      StringToInt (result.dropRight 1) = ComputeSubsetSumWays n s a % 998244353
  else
    result = "0\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
