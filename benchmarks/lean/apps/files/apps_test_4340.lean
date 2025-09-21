-- <vc-preamble>
def TransformElement (x : Int) : Int :=
  if x % 2 = 0 then x - 1 else x

def ValidTransformation (input output : List Int) : Prop :=
  output.length = input.length ∧
  ∀ i, 0 ≤ i ∧ i < input.length → output.get! i = TransformElement (input.get! i)

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : List Int) (h_precond : solve_precond a) : Prop :=
  ValidTransformation a result

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>