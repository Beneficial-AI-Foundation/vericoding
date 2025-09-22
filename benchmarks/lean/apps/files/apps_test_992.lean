-- <vc-preamble>
def ValidInput (n s : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ n ≤ 3000 ∧
  s ≥ 1 ∧ s ≤ 3000 ∧
  a.length = n ∧
  ∀ i, 0 ≤ i ∧ i < n → a[i.natAbs]! ≥ 1 ∧ a[i.natAbs]! ≤ 3000

def ComputeDPTable (n : Nat) (s : Nat) (a : List Int) : List (List Int) :=
  match n with
  | 0 => []
  | 1 => 
    let base : List Int := List.replicate (s + 1) 0 |>.mapIdx (fun j _ => if j = 0 then 1 else 0)
    let new_row : List Int := List.range (s + 1) |>.map (fun j =>
      let doubled := (base[j]! * 2) % 998244353
      if j ≥ (a[0]!).natAbs ∧ j - (a[0]!).natAbs < s + 1 then
        (doubled + base[j - (a[0]!).natAbs]!) % 998244353
      else
        doubled)
    [base, new_row]
  | n + 1 =>
    let prev_dp := ComputeDPTable n s (a.take n)
    let new_row : List Int := List.range (s + 1) |>.map (fun j =>
      let doubled := (prev_dp[n]![j]! * 2) % 998244353
      if j ≥ (a[n]!).natAbs ∧ j - (a[n]!).natAbs < s + 1 then
        (doubled + prev_dp[n]![j - (a[n]!).natAbs]!) % 998244353
      else
        doubled)
    prev_dp ++ [new_row]

def ComputeSubsetSumWays (n s : Int) (a : List Int) : Int :=
  let dp := ComputeDPTable n.natAbs s.natAbs a
  if dp.length > n.natAbs ∧ dp[n.natAbs]!.length > s.natAbs then 
    dp[n.natAbs]![s.natAbs]! 
  else 
    0

def SplitLines (_s : String) : List String := ["", ""]

def SplitWhitespace (_s : String) : List String := [""]

def StringToInt (_s : String) : Int := 0

def IntToString (_n : Int) : String := "0"

def ValidParsedInput (input : String) (n s : Int) (a : List Int) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 2 ∧
  let first_line := SplitWhitespace lines[0]!
  let second_line := SplitWhitespace lines[1]!
  first_line.length ≥ 2 ∧ second_line.length = n ∧
  n = StringToInt first_line[0]! ∧
  s = StringToInt first_line[1]! ∧
  a.length = n ∧
  (∀ i, 0 ≤ i ∧ i < n → a[i.natAbs]! = StringToInt second_line[i.natAbs]!) ∧
  ValidInput n s a

def ValidParsedInputExists (input : String) : Bool :=
  let lines := SplitLines input
  if lines.length < 2 then false
  else
    let first_line := SplitWhitespace lines[0]!
    let second_line := SplitWhitespace lines[1]!
    if first_line.length < 2 ∨ second_line.length = 0 then false
    else
      let n := StringToInt first_line[0]!
      let s := StringToInt first_line[1]!
      (n ≥ 1 ∧ n ≤ 3000 ∧ s ≥ 1 ∧ s ≤ 3000 ∧ second_line.length = n) &&
      (List.range n.natAbs).all (fun i =>
        let ai := StringToInt second_line[i]!
        ai ≥ 1 ∧ ai ≤ 3000)

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧ 
  result.data[result.length - 1]! = '\n' ∧
  (if ValidParsedInputExists stdin_input then
    ∃ n s a, ValidParsedInput stdin_input n s a ∧
      StringToInt (result.take (result.length - 1)) = ComputeSubsetSumWays n s a % 998244353
  else
    result = "0\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>