-- <vc-preamble>
def UnitWord (n : Int) : String :=
  if n = 1 then "one"
  else if n = 2 then "two"
  else if n = 3 then "three"
  else if n = 4 then "four"
  else if n = 5 then "five"
  else if n = 6 then "six"
  else if n = 7 then "seven"
  else if n = 8 then "eight"
  else if n = 9 then "nine"
  else ""

def IsValidIntegerString (s : String) : Prop :=
  (s.length ≥ 1 ∧ s.length ≤ 3 ∧ ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9') ∨
  (s.length ≥ 2 ∧ s.length ≤ 4 ∧ s.data[s.length-1]! = '\n' ∧ ∀ i, 0 ≤ i ∧ i < s.length-1 → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9')

def ParseIntegerHelper (s : String) : Int :=
  if s.length = 1 then
    (s.data[0]!).toNat - ('0').toNat
  else if s.length = 2 then
    10 * ((s.data[0]!).toNat - ('0').toNat) + ((s.data[1]!).toNat - ('0').toNat)
  else
    100 * ((s.data[0]!).toNat - ('0').toNat) + 10 * ((s.data[1]!).toNat - ('0').toNat) + ((s.data[2]!).toNat - ('0').toNat)

def ParseInteger (s : String) : Int :=
  if s.length > 0 ∧ s.data[s.length-1]! = '\n' then
    ParseIntegerHelper (s.dropRight 1)
  else
    ParseIntegerHelper s

def CorrectEnglishWord (n : Int) : String :=
  if n = 0 then "zero"
  else if n = 1 then "one"
  else if n = 2 then "two"
  else if n = 3 then "three"
  else if n = 4 then "four"
  else if n = 5 then "five"
  else if n = 6 then "six"
  else if n = 7 then "seven"
  else if n = 8 then "eight"
  else if n = 9 then "nine"
  else if n = 10 then "ten"
  else if n = 11 then "eleven"
  else if n = 12 then "twelve"
  else if n = 13 then "thirteen"
  else if n = 14 then "fourteen"
  else if n = 15 then "fifteen"
  else if n = 16 then "sixteen"
  else if n = 17 then "seventeen"
  else if n = 18 then "eighteen"
  else if n = 19 then "nineteen"
  else if n = 20 then "twenty"
  else if n = 30 then "thirty"
  else if n = 40 then "forty"
  else if n = 50 then "fifty"
  else if n = 60 then "sixty"
  else if n = 70 then "seventy"
  else if n = 80 then "eighty"
  else if n = 90 then "ninety"
  else if 21 ≤ n ∧ n ≤ 29 then "twenty-" ++ UnitWord (n % 10)
  else if 31 ≤ n ∧ n ≤ 39 then "thirty-" ++ UnitWord (n % 10)
  else if 41 ≤ n ∧ n ≤ 49 then "forty-" ++ UnitWord (n % 10)
  else if 51 ≤ n ∧ n ≤ 59 then "fifty-" ++ UnitWord (n % 10)
  else if 61 ≤ n ∧ n ≤ 69 then "sixty-" ++ UnitWord (n % 10)
  else if 71 ≤ n ∧ n ≤ 79 then "seventy-" ++ UnitWord (n % 10)
  else if 81 ≤ n ∧ n ≤ 89 then "eighty-" ++ UnitWord (n % 10)
  else "ninety-" ++ UnitWord (n % 10)

def ValidInput (s : String) : Prop :=
  IsValidIntegerString s ∧ 
  let n := ParseInteger s
  0 ≤ n ∧ n ≤ 99

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
  result.length > 0 ∧ 
  result.data[result.length-1]! = '\n' ∧
  let n := ParseInteger stdin_input
  result = CorrectEnglishWord n ++ "\n"

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>