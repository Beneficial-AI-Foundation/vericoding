import Mathlib
-- <vc-preamble>
def ValidInput (N : Int) : Prop :=
  1 ≤ N ∧ N ≤ 999

def IsHonDigit (digit : Int) : Bool :=
  digit = 2 || digit = 4 || digit = 5 || digit = 7 || digit = 9

def IsPonDigit (digit : Int) : Bool :=
  digit = 0 || digit = 1 || digit = 6 || digit = 8

def IsBonDigit (digit : Int) : Bool :=
  digit = 3

def CorrectPronunciation (N : Int) (h : ValidInput N) : String :=
  let ones_digit := N % 10
  if IsHonDigit ones_digit then "hon\n"
  else if IsPonDigit ones_digit then "pon\n"
  else "bon\n"

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : String :=
  CorrectPronunciation N h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : String) (h_precond : solve_precond N) : Prop :=
  result = CorrectPronunciation N h_precond

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  simpa [solve_postcond, solve]
-- </vc-theorems>
