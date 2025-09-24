-- <vc-preamble>
def IsVowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u'

def IsOddDigit (c : Char) : Bool :=
  c = '1' || c = '3' || c = '5' || c = '7' || c = '9'

def NeedsFlipping (c : Char) : Bool :=
  IsVowel c || IsOddDigit c

def CountFlips (s : String) : Int :=
  (s.toList.filter NeedsFlipping).length

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length ≥ 1 ∧ s.length ≤ 50
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  result.length > 0 ∧ result = toString (CountFlips s) ++ "\n"

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>