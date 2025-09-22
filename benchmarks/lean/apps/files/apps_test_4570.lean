-- <vc-preamble>

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧ 
  (s.get 0 = '-' ∨ ('0' ≤ s.get 0 ∧ s.get 0 ≤ '9')) ∧
  ∀ i, 1 ≤ i ∧ i < s.length → '0' ≤ s.get ⟨i⟩ ∧ s.get ⟨i⟩ ≤ '9'

def SplitStringHelper (s : String) (i : Nat) (start : Nat) (acc : List String) : List String :=
  if h : i ≥ s.length then
    if i > start then acc ++ [s.extract ⟨start⟩ ⟨i⟩] else acc
  else if s.get ⟨i⟩ = ' ' ∨ s.get ⟨i⟩ = '\n' ∨ s.get ⟨i⟩ = '\r' then
    let newAcc := if i > start then acc ++ [s.extract ⟨start⟩ ⟨i⟩] else acc
    SplitStringHelper s (i + 1) (i + 1) newAcc
  else
    SplitStringHelper s (i + 1) start acc
termination_by s.length - i

def SplitStringFunc (s : String) : List String :=
  SplitStringHelper s 0 0 []

def StringToIntHelper (s : String) (i : Nat) (acc : Int) : Int :=
  if h : i ≥ s.length then acc
  else if '0' ≤ s.get ⟨i⟩ ∧ s.get ⟨i⟩ ≤ '9' then
    StringToIntHelper s (i + 1) (acc * 10 + Int.ofNat ((s.get ⟨i⟩).toNat - '0'.toNat))
  else
    StringToIntHelper s (i + 1) acc
termination_by s.length - i

def StringToIntFunc (s : String) : Int :=
  if s.length > 0 ∧ s.get 0 = '-' then
    -(StringToIntHelper s 1 0)
  else
    StringToIntHelper s 0 0

partial def IntToStringHelper (n : Int) (acc : String) : String :=
  if n = 0 then acc
  else
    let digit := n % 10
    IntToStringHelper (n / 10) (String.mk [Char.ofNat ('0'.toNat + digit.natAbs)] ++ acc)

def IntToStringFunc (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringHelper (-n) ""
  else IntToStringHelper n ""

def MinParkingCost (n : Int) (a : Int) (b : Int) : Int :=
  let plan1Cost := n * a
  let plan2Cost := b
  if plan1Cost ≤ plan2Cost then plan1Cost else plan2Cost

def ValidInput (input : String) : Prop :=
  let parts := SplitStringFunc input
  parts.length ≥ 3 ∧ 
  (∀ i, 0 ≤ i ∧ i < 3 → parts[i]!.length > 0 ∧ IsValidInteger parts[i]!) ∧
  let n := StringToIntFunc parts[0]!
  let a := StringToIntFunc parts[1]!
  let b := StringToIntFunc parts[2]!
  1 ≤ n ∧ n ≤ 20 ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 2000

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
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
  ∃ n a b, 
    let parts := SplitStringFunc input
    n = StringToIntFunc parts[0]! ∧
    a = StringToIntFunc parts[1]! ∧ 
    b = StringToIntFunc parts[2]! ∧
    result = IntToStringFunc (MinParkingCost n a b) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>