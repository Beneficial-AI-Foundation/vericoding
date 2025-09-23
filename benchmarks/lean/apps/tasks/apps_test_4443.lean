-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 'a' ≤ input.data.get! 0 ∧ input.data.get! 0 ≤ 'y'

def NextChar (c : Char) : Char :=
  Char.ofNat (c.toNat + 1)

def ValidOutput (input output : String) : Prop :=
  ValidInput input →
  (output.length = 2 ∧
   output.data.get! 0 = NextChar (input.data.get! 0) ∧
   output.data.get! 1 = '\n' ∧
   'b' ≤ output.data.get! 0 ∧ output.data.get! 0 ≤ 'z')

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
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput input output

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>