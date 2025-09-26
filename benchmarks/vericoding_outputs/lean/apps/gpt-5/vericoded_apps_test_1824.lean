import Mathlib
-- <vc-preamble>
-- String helper functions for parsing
partial def FindChar (s : String) (c : Char) (start : Nat) : Int :=
  if h : start < s.length then
    if s.get (String.Pos.mk start) = c then start
    else FindChar s c (start + 1)
  else -1

partial def SplitByChar (s : String) (delimiter : Char) : List String :=
  if s.length = 0 then []
  else
    let pos := FindChar s delimiter 0
    if pos = -1 then [s]
    else if pos = 0 then SplitByChar (s.drop 1) delimiter
    else [s.take pos.natAbs] ++ SplitByChar (s.drop (pos.natAbs + 1)) delimiter

def SplitBySpace (s : String) : List String :=
  SplitByChar s ' '

partial def SplitByNewline (s : String) : List String :=
  if s.length = 0 then []
  else if s.get! 0 = '\n' then SplitByNewline (s.drop 1)
  else 
    let rest := SplitByNewline (s.drop 1)
    if rest.length = 0 then [s]
    else [(s.take 1) ++ rest.head!] ++ rest.tail!

partial def StringToIntHelper (s : String) (acc : Int) : Int :=
  if s.length = 0 then acc
  else if '0' ≤ s.get! 0 ∧ s.get! 0 ≤ '9' then
    StringToIntHelper (s.drop 1) (acc * 10 + (s.get! 0).toNat - '0'.toNat)
  else acc

def StringToInt (s : String) : Int :=
  if s.length = 0 then 0
  else if s.get! 0 = '-' then -(StringToIntHelper (s.drop 1) 0)
  else StringToIntHelper s 0

partial def IntToStringHelper (n : Int) : String :=
  if n = 0 then ""
  else IntToStringHelper (n / 10) ++ String.mk [Char.ofNat ((n % 10).natAbs + '0'.toNat)]

def IntToString (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringHelper (-n)
  else IntToStringHelper n

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧ (s.get! 0 = '-' → s.length > 1) ∧ 
  (∀ i : Nat, (if s.get! 0 = '-' then 1 else 0) ≤ i ∧ i < s.length → '0' ≤ s.get (String.Pos.mk i) ∧ s.get (String.Pos.mk i) ≤ '9')

partial def SumSequence (numbers : List String) : Int :=
  match numbers with
  | [] => 0
  | head :: tail => StringToInt head + SumSequence tail

def GetFirstSum (input : String) : Int :=
  let lines := SplitByNewline input
  let firstLine := SplitBySpace (lines[1]!)
  SumSequence firstLine

def GetSecondSum (input : String) : Int :=
  let lines := SplitByNewline input
  let secondLine := SplitBySpace (lines[2]!)
  SumSequence secondLine

def GetThirdSum (input : String) : Int :=
  let lines := SplitByNewline input
  let thirdLine := SplitBySpace (lines[3]!)
  SumSequence thirdLine

def ValidInput (input : String) : Prop :=
  let lines := SplitByNewline input
  lines.length ≥ 4 ∧ 
  IsValidInteger (lines[0]!) ∧
  StringToInt (lines[0]!) ≥ 3 ∧
  (SplitBySpace (lines[1]!)).length = StringToInt (lines[0]!) ∧
  (SplitBySpace (lines[2]!)).length = StringToInt (lines[0]!) - 1 ∧
  (SplitBySpace (lines[3]!)).length = StringToInt (lines[0]!) - 2 ∧
  (∀ i : Nat, 0 ≤ i ∧ i < (SplitBySpace (lines[1]!)).length → IsValidInteger ((SplitBySpace (lines[1]!))[i]!)) ∧
  (∀ i : Nat, 0 ≤ i ∧ i < (SplitBySpace (lines[2]!)).length → IsValidInteger ((SplitBySpace (lines[2]!))[i]!)) ∧
  (∀ i : Nat, 0 ≤ i ∧ i < (SplitBySpace (lines[3]!)).length → IsValidInteger ((SplitBySpace (lines[3]!))[i]!))

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def computeOutput (a b c : Int) : String :=
  IntToString (a - b) ++ "\n" ++ IntToString (b - c) ++ "\n"
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  computeOutput (GetFirstSum input) (GetSecondSum input) (GetThirdSum input)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = IntToString (GetFirstSum input - GetSecondSum input) ++ "\n" ++ IntToString (GetSecondSum input - GetThirdSum input) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  rfl
-- </vc-theorems>
