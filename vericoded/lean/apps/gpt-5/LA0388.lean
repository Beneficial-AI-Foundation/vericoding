import Mathlib
-- <vc-preamble>
def ValidGrid (grid : List (List Int)) : Prop :=
  grid.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < grid.length → (grid[i]!).length > 0

def seq_min : List Int → Int
  | [] => 0  -- dummy case, shouldn't be reached with precondition
  | [x] => x
  | x :: xs => if x ≤ seq_min xs then x else seq_min xs

def seq_max : List Int → Int
  | [] => 0  -- dummy case, shouldn't be reached with precondition  
  | [x] => x
  | x :: xs => if x ≥ seq_max xs then x else seq_max xs

@[reducible, simp]
def solve_precond (grid : List (List Int)) : Prop :=
  ValidGrid grid
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma seq_min_nil : seq_min ([] : List Int) = 0 := rfl
-- LLM HELPER
@[simp] lemma seq_max_nil : seq_max ([] : List Int) = 0 := rfl
-- LLM HELPER
@[simp] lemma seq_min_singleton (x : Int) : seq_min [x] = x := rfl
-- LLM HELPER
@[simp] lemma seq_max_singleton (x : Int) : seq_max [x] = x := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (grid : List (List Int)) (h_precond : solve_precond grid) : Int :=
  let row_mins := grid.map seq_min
  seq_max row_mins
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (grid : List (List Int)) (result : Int) (h_precond : solve_precond grid) : Prop :=
  let row_mins := grid.map seq_min
  result = seq_max row_mins

theorem solve_spec_satisfied (grid : List (List Int)) (h_precond : solve_precond grid) :
    solve_postcond grid (solve grid h_precond) h_precond := by
  unfold solve_postcond
  simpa [solve]
-- </vc-theorems>
