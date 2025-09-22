-- <vc-preamble>
def max_of_seq (s : List Int) : Int :=
  match s with
  | [] => 0
  | [x] => x
  | x :: xs => max x (max_of_seq xs)

def max_excluding (s : List Int) (exclude_idx : Int) : Int :=
  let others := (s.take exclude_idx.natAbs) ++ (s.drop (exclude_idx.natAbs + 1))
  max_of_seq others

@[reducible, simp]
def solve_precond (input : List Int) : Prop :=
  input.length ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : List Int) (h_precond : solve_precond input) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : List Int) (result : List Int) (h_precond : solve_precond input) : Prop :=
  result.length = input.length ∧ 
  ∀ i, 0 ≤ i ∧ i < input.length → 
    result.get! i = max_excluding input i

theorem solve_spec_satisfied (input : List Int) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>