-- <vc-preamble>
def CharToDigit (c : Char) : Int :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat : Int) else 0

def StringToInt (s : String) : Int :=
  let chars := s.toList
  if chars.length = 0 then 0
  else if chars.length = 1 then CharToDigit chars[0]!
  else if chars.length = 2 then CharToDigit chars[0]! * 10 + CharToDigit chars[1]!
  else if chars.length = 4 then CharToDigit chars[0]! * 1000 + CharToDigit chars[1]! * 100 + CharToDigit chars[2]! * 10 + CharToDigit chars[3]!
  else 0

def IsValidDateString (s : String) (y m d : Int) : Prop :=
  let chars := s.toList
  s.length ≥ 10 ∧ 
  (if h : 4 < chars.length then chars[4]! = '/' else False) ∧ 
  (if h : 7 < chars.length then chars[7]! = '/' else False) ∧
  StringToInt (s.take 4) = y ∧
  StringToInt (s.drop 5 |>.take 2) = m ∧
  StringToInt (s.drop 8 |>.take 2) = d

def ValidInput (s : String) : Prop :=
  ∃ y m d, IsValidDateString s y m d ∧ y = 2019 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31

def CorrectOutput (s : String) (result : String) : Prop :=
  ∃ y m d, IsValidDateString s y m d ∧ y = 2019 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31 ∧ 
  ((m < 4 ∨ (m = 4 ∧ d ≤ 30)) → result = "Heisei") ∧ 
  ((m > 4 ∨ (m = 4 ∧ d > 30)) → result = "TBD")

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInput stdin_input
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
  CorrectOutput stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>