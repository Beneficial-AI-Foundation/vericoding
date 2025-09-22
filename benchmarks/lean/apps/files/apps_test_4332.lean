-- <vc-preamble>
def IsDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def DigitValue (c : Char) : Int :=
  Int.ofNat (c.toNat - '0'.toNat)

def SumOfDigits (s : String) : Int :=
  s.data.foldl (fun acc c => if IsDigit c then acc + Int.ofNat (c.toNat - '0'.toNat) else acc) 0

def StringToInt (s : String) : Int :=
  s.data.foldl (fun acc c => if IsDigit c then acc * 10 + Int.ofNat (c.toNat - '0'.toNat) else acc) 0

def Power10 (n : Nat) : Int :=
  Int.ofNat (10 ^ n)

def CleanInput (input : String) : String :=
  input.trim

def ValidPositiveIntegerString (s : String) : Prop :=
  s.length > 0 ∧ 
  (∀ i, i < s.length → IsDigit (s.get (String.Pos.mk i)) = true) ∧ 
  (s.length > 1 → s.get (String.Pos.mk 0) ≠ '0') ∧ 
  StringToInt s > 0

def ValidInput (input : String) : Prop :=
  ValidPositiveIntegerString (CleanInput input)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  let cleaned := CleanInput input
  let n := StringToInt cleaned
  let digitSum := SumOfDigits cleaned
  (result = "Yes" ∨ result = "No") ∧
  (digitSum > 0 ∧ 
   ((result = "Yes") ↔ (n % digitSum = 0)) ∧
   ((result = "No") ↔ (n % digitSum ≠ 0))) ∧
  (n ≥ 1)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>