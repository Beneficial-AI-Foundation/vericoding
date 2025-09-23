-- <vc-preamble>

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (∃ i, 0 < i ∧ i < input.length ∧ input.data[i]! = '\n') ∧
  (∀ i, 0 ≤ i ∧ i < input.length → input.data[i]! = '\n' ∨ ('0' ≤ input.data[i]! ∧ input.data[i]! ≤ '9') ∨ ('a' ≤ input.data[i]! ∧ input.data[i]! ≤ 'z')) ∧
  (∃ i, 0 < i ∧ i < input.length ∧ input.data[i]! = '\n' ∧ (∀ j, 0 ≤ j ∧ j < i → '0' ≤ input.data[j]! ∧ input.data[j]! ≤ '9'))

def ValidParsedInput (a : Int) (s : String) : Prop :=
  2800 ≤ a ∧ a < 5000 ∧
  1 ≤ s.length ∧ s.length ≤ 10 ∧
  (∀ j, 0 ≤ j ∧ j < s.length → 'a' ≤ s.data[j]! ∧ s.data[j]! ≤ 'z')

def CorrectOutput (a : Int) (s : String) (result : String) : Prop :=
  (a ≥ 3200 → result = s ++ "\n") ∧
  (a < 3200 → result = "red\n")

axiom parseInput : String → Int × String

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input ∧
  (∃ a s, parseInput input = (a, s) ∧ ValidParsedInput a s)
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
  (∃ a s, parseInput input = (a, s) ∧ ValidParsedInput a s ∧ CorrectOutput a s result) ∧
  result.length > 0 ∧
  result.data[result.length - 1]! = '\n' ∧
  ((∃ a s, parseInput input = (a, s) ∧ a ≥ 3200) → 
    (∃ s, result = s ++ "\n" ∧ 1 ≤ s.length ∧ s.length ≤ 10 ∧ (∀ j, 0 ≤ j ∧ j < s.length → 'a' ≤ s.data[j]! ∧ s.data[j]! ≤ 'z'))) ∧
  ((∃ a s, parseInput input = (a, s) ∧ a < 3200) → result = "red\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>