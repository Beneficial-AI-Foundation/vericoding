-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length = 1 ∧ 'a' ≤ input.get! 0 ∧ input.get! 0 ≤ 'z'

def IsVowel (c : Char) : Bool :=
  c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u'

def ExpectedOutput (input : String) (h : ValidInput input) : String :=
  if IsVowel (input.get! 0) then "vowel" else "consonant"

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
  result = ExpectedOutput input h_precond ∧ (result = "vowel" ∨ result = "consonant")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>