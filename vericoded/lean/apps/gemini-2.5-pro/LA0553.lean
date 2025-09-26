import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 4 ∧ ∀ i, 0 ≤ i ∧ i < 4 → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def charPairToInt (c1 c2 : Char) : Int :=
  (c1.toNat - '0'.toNat) * 10 + (c2.toNat - '0'.toNat)

def ValidMonth (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 12

def GetFirstPair (s : String) : Int :=
  charPairToInt s.data[0]! s.data[1]!

def GetSecondPair (s : String) : Int :=
  charPairToInt s.data[2]! s.data[3]!

def CorrectResult (s : String) (result : String) : Prop :=
  let s1 := GetFirstPair s
  let s2 := GetSecondPair s
  let s1_valid := ValidMonth s1
  let s2_valid := ValidMonth s2
  (s1_valid ∧ s2_valid → result = "AMBIGUOUS\n") ∧
  (s1_valid ∧ ¬s2_valid → result = "MMYY\n") ∧
  (¬s1_valid ∧ s2_valid → result = "YYMM\n") ∧
  (¬s1_valid ∧ ¬s2_valid → result = "NA\n")

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
instance {n : Int} : Decidable (ValidMonth n) := by
  unfold ValidMonth
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  let s1 := GetFirstPair stdin_input
  let s2 := GetSecondPair stdin_input
  if ValidMonth s1 then
    if ValidMonth s2 then
      "AMBIGUOUS\n"
    else
      "MMYY\n"
  else
    if ValidMonth s2 then
      "YYMM\n"
    else
      "NA\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result ∈ ["AMBIGUOUS\n", "MMYY\n", "YYMM\n", "NA\n"] ∧
  CorrectResult stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  simp [solve, solve_postcond, CorrectResult, GetFirstPair, GetSecondPair]
  split_ifs <;> simp_all
-- </vc-theorems>
