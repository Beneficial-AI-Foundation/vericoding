-- <vc-preamble>
def intToString (n : Int) : String := toString n

def stringToInt (s : String) : Int := s.toInt!

def splitOnSpace (s : String) : List String := s.splitOn " "

def stringGet (s : String) (i : Nat) : Char :=
  if i < s.length then s.get (String.Pos.mk i) else default

def isPalindromicDecidable (n : Int) : Bool :=
  if n < 0 then false
  else
    let s := intToString n
    let len := s.length
    let rec check (i : Nat) : Bool :=
      if i >= len / 2 then true
      else if stringGet s i = stringGet s (len - 1 - i) then check (i + 1)
      else false
    check 0

@[reducible, simp]
def isPalindromic (n : Int) : Prop :=
  n ≥ 0 → isPalindromicDecidable n = true

partial def countPalindromicNumbers (a b : Int) : Int :=
  if a > b then 0
  else if a = b then (if isPalindromicDecidable a then 1 else 0)
  else (if isPalindromicDecidable a then 1 else 0) + countPalindromicNumbers (a + 1) b

@[reducible, simp]
def isValidInteger (s : String) : Prop :=
  s.length > 0 ∧ ∀ i : Nat, i < s.length → '0' ≤ stringGet s i ∧ stringGet s i ≤ '9'

@[reducible, simp]
def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (∃ i : Nat, i < stdin_input.length ∧ stringGet stdin_input i = ' ') ∧
  let parts := splitOnSpace stdin_input
  parts.length = 2 ∧ 
  isValidInteger parts[0]! ∧ 
  isValidInteger parts[1]! ∧
  stringToInt parts[0]! ≥ 10000 ∧
  stringToInt parts[1]! ≥ 10000 ∧
  stringToInt parts[0]! ≤ 99999 ∧
  stringToInt parts[1]! ≤ 99999 ∧
  stringToInt parts[0]! ≤ stringToInt parts[1]!

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧
  stringGet result (result.length - 1) = '\n' ∧
  let parts := splitOnSpace stdin_input
  let a := stringToInt parts[0]!
  let b := stringToInt parts[1]!
  result = intToString (countPalindromicNumbers a b) ++ "\n"

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>