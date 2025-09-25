-- <vc-preamble>
def IsVowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u' || c = 'y'

def NoConsecutiveVowels (s : List Char) : Prop :=
  ∀ i, 0 ≤ i ∧ i < s.length - 1 → ¬(IsVowel s[i]! ∧ IsVowel s[i+1]!)

def ValidOutput (input output : List Char) : Prop :=
  output.length ≤ input.length ∧
  NoConsecutiveVowels output ∧
  (input.length > 0 → output.length > 0) ∧
  (input.length > 0 → output[0]! = input[0]!)

@[reducible, simp]
def solve_precond (s : List Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : List Char) (h_precond : solve_precond s) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : List Char) (result : List Char) (h_precond : solve_precond s) : Prop :=
  ValidOutput s result

theorem solve_spec_satisfied (s : List Char) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>