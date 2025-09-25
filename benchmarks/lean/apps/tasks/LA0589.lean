-- <vc-preamble>
def ValidInput (input : List (Int × Int)) : Prop :=
  ∀ i, i < input.length → input[i]!.1 ≥ 1 ∧ input[i]!.2 ≥ 1

def MinMoves (a b : Int) : Int :=
  if a ≥ 1 ∧ b ≥ 1 then
    if a = b then 0
    else if a < b then
      if (b - a) % 2 = 1 then 1 else 2
    else
      if (a - b) % 2 = 0 then 1 else 2
  else 0

def ValidOutput (input : List (Int × Int)) (result : List Int) : Prop :=
  ValidInput input →
  result.length = input.length ∧
  (∀ i, i < input.length → result[i]! = MinMoves input[i]!.1 input[i]!.2) ∧
  (∀ i, i < result.length → result[i]! ≥ 0)

@[reducible, simp]
def solve_precond (input : List (Int × Int)) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : List (Int × Int)) (h_precond : solve_precond input) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : List (Int × Int)) (result : List Int) (h_precond : solve_precond input) : Prop :=
  ValidOutput input result

theorem solve_spec_satisfied (input : List (Int × Int)) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>