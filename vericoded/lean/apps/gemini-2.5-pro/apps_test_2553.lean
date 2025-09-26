import Mathlib
-- <vc-preamble>

def CountLines (s : String) : Nat :=
  if s.length = 0 then 0 else 1

def GetLine (s : String) (line_index : Nat) : String :=
  if line_index = 0 then "No" else ""

def ParseFirstLine (input : String) : Nat := 1

def GetTestCaseN (input : String) (case_index : Nat) : Nat := 1

def GetTestCaseX (input : String) (case_index : Nat) : Nat := 1

def GetTestCaseArray (input : String) (case_index : Nat) : List Int := [1]

def CountOddElements (arr : List Int) : Nat :=
  match arr with
  | [] => 0
  | head :: tail => 
      if head % 2 = 1 then 1 + CountOddElements tail
      else CountOddElements tail

def CanSelectOddSum (arr : List Int) (x : Nat) : Bool :=
  let odd_count := CountOddElements arr
  let even_count := arr.length - odd_count
  
  if x = arr.length then
      odd_count % 2 = 1
  else if odd_count > 0 ∧ even_count > 0 then
      true
  else if even_count = 0 then
      x % 2 = 1
  else
      false

def ValidTestCasesFormat (input : String) (q : Nat) : Prop :=
  ∀ i, 0 ≤ i ∧ i < q → 
      ∃ n x : Nat, (1 ≤ x ∧ x ≤ n ∧ n ≤ 1000 ∧
      GetTestCaseN input i = n ∧
      GetTestCaseX input i = x ∧
      (GetTestCaseArray input i).length = n ∧
      ∀ j, 0 ≤ j ∧ j < n → 1 ≤ (GetTestCaseArray input i)[j]! ∧ (GetTestCaseArray input i)[j]! ≤ 1000)

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ input.data[input.length - 1]! = '\n' ∧
  CountLines input ≥ 1 ∧
  ∃ q : Nat, (1 ≤ q ∧ q ≤ 100 ∧ 
      ParseFirstLine input = q ∧
      CountLines input = 1 + 2 * q ∧
      ValidTestCasesFormat input q)

def ValidOutput (output : String) : Prop :=
  output.length ≥ 0 ∧ 
  (output.length = 0 ∨ output.data[output.length - 1]! = '\n') ∧
  ∀ i, 0 ≤ i ∧ i < CountLines output → 
      (GetLine output i = "Yes" ∨ GetLine output i = "No")

def OutputMatchesAlgorithm (input : String) (output : String) : Prop :=
  let q := ParseFirstLine input
  CountLines output = q ∧
  ∀ i, 0 ≤ i ∧ i < q →
      let arr := GetTestCaseArray input i
      let x := GetTestCaseX input i
      let expected := if CanSelectOddSum arr x then "Yes" else "No"
      GetLine output i = expected

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def solve_aux (stdin_input : String) (i : Nat) (q : Nat) : String :=
  if i < q then
    let arr := GetTestCaseArray stdin_input i
    let x := GetTestCaseX stdin_input i
    let result := if CanSelectOddSum arr x then "Yes\n" else "No\n"
    result ++ solve_aux stdin_input (i + 1) q
  else
    ""
termination_by q - i

-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let q := ParseFirstLine stdin_input
  solve_aux stdin_input 0 q
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (output : String) (h_precond : solve_precond stdin_input) : Prop :=
  ValidOutput output ∧
  OutputMatchesAlgorithm stdin_input output ∧
  CountLines output = ParseFirstLine stdin_input ∧
  ∀ i, 0 ≤ i ∧ i < CountLines output → 
      (GetLine output i = "Yes" ∨ GetLine output i = "No")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  exfalso
  -- The precondition `solve_precond stdin_input` is unsatisfiable because the
  -- definitions of `CountLines` and `ParseFirstLine` are contradictory with
  -- the properties required by `ValidInput`.
  unfold solve_precond ValidInput at h_precond
  -- Dig out the contradictory parts from the precondition.
  rcases h_precond with ⟨_, _, _, q, ⟨_, _, h_parse, h_lines, _⟩⟩
  -- `h_parse` is `ParseFirstLine stdin_input = q`
  -- `h_lines` is `CountLines stdin_input = 1 + 2 * q`
  -- From its definition, `ParseFirstLine` always returns 1, so `q` must be 1.
  -- We substitute this into the equation for `h_lines`.
  rw [← h_parse] at h_lines
  -- Now unfold the function definitions to show the contradiction.
  unfold CountLines ParseFirstLine at h_lines
  -- `h_lines` becomes `(if stdin_input.length = 0 then 0 else 1) = 1 + 2 * 1`.
  -- `simp` will evaluate the right side to 3.
  simp at h_lines
  -- This equality can never hold. We can split on the `if` condition to show this.
  split at h_lines <;> simp_all
-- </vc-theorems>
