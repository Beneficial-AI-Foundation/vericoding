-- <vc-preamble>
def ValidInput (word : String) : Prop :=
  word.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < word.length → 
    ('a' ≤ word.data[i]! ∧ word.data[i]! ≤ 'z') ∨ 
    ('A' ≤ word.data[i]! ∧ word.data[i]! ≤ 'Z')

def CorrectCapitalization (input output : String) (h_valid : ValidInput input) : Prop :=
  output.length = input.length ∧
  ('A' ≤ output.data[0]! ∧ output.data[0]! ≤ 'Z') ∧
  (('a' ≤ input.data[0]! ∧ input.data[0]! ≤ 'z') → 
    ('A' ≤ output.data[0]! ∧ output.data[0]! ≤ 'Z')) ∧
  (('A' ≤ input.data[0]! ∧ input.data[0]! ≤ 'Z') → 
    (output.data[0]! = input.data[0]!)) ∧
  ∀ i, 1 ≤ i ∧ i < input.length → output.data[i]! = input.data[i]!

@[reducible, simp]
def solve_precond (word : String) : Prop :=
  ValidInput word
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (word : String) (h_precond : solve_precond word) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (word : String) (result : String) (h_precond : solve_precond word) : Prop :=
  CorrectCapitalization word result h_precond

theorem solve_spec_satisfied (word : String) (h_precond : solve_precond word) :
    solve_postcond word (solve word h_precond) h_precond := by
  sorry
-- </vc-theorems>