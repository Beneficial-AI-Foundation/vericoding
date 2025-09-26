import Mathlib
-- <vc-preamble>
def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0

partial def SplitLinesFuncHelper (s : String) (i : Nat) (current : String) (acc : List String) : List String :=
  if i >= s.length then
    if current = "" then acc else acc ++ [current]
  else if s.get ⟨i⟩ = '\n' then
    SplitLinesFuncHelper s (i + 1) "" (acc ++ [current])
  else
    SplitLinesFuncHelper s (i + 1) (current ++ (s.get ⟨i⟩).toString) acc

def SplitLinesFunc (s : String) : List String :=
  SplitLinesFuncHelper s 0 "" []

partial def StringToIntHelper (s : String) : Int :=
  if s.length = 0 then 0
  else StringToIntHelper (s.dropRight 1) * 10 + Int.ofNat (s.back.toNat - '0'.toNat)

def StringToInt (s : String) : Int :=
  if s.length = 0 then 0
  else if s.front = '-' then -(StringToIntHelper (s.drop 1))
  else StringToIntHelper s

partial def IntToStringHelper (n : Int) : String :=
  if n = 0 then ""
  else IntToStringHelper (n / 10) ++ (Char.ofNat (Int.natAbs (n % 10) + '0'.toNat)).toString

def IntToString (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringHelper (-n)
  else IntToStringHelper n

def ExpectedOutput (stdin_input : String) : String :=
  let lines := SplitLinesFunc stdin_input
  if lines.length ≥ 1 then
    let n := StringToInt (lines.get! 0)
    if n = 1 then "Hello World\n"
    else if n ≠ 1 ∧ lines.length ≥ 3 then
      let a := StringToInt (lines.get! 1)
      let b := StringToInt (lines.get! 2)
      IntToString (a + b) ++ "\n"
    else ""
  else ""

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma precond_to_valid {s : String} (h : solve_precond s) : ValidInput s := h
-- LLM HELPER
@[simp] lemma valid_to_precond {s : String} (h : ValidInput s) : solve_precond s := h
-- LLM HELPER
@[simp] lemma solve_precond_iff_valid (s : String) : solve_precond s = ValidInput s := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  ExpectedOutput stdin_input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result = ExpectedOutput stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  simp [solve]
-- </vc-theorems>
