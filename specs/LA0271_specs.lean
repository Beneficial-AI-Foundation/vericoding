-- <vc-preamble>

def count_occurrences (s : List Int) (value : Int) : Int :=
  match s with
  | [] => 0
  | head :: tail => (if head = value then 1 else 0) + count_occurrences tail value

def ValidInput (n : Int) (m : Int) (squares : List Int) : Prop :=
  n ≥ 1 ∧ n ≤ 1000 ∧
  m ≥ 1 ∧ m ≤ 1000 ∧
  squares.length = m ∧
  ∀ i, 0 ≤ i ∧ i < squares.length → 1 ≤ squares.get! i ∧ squares.get! i ≤ n

def CorrectResult (n : Int) (squares : List Int) (result : Int) : Prop :=
  0 ≤ result ∧ result ≤ squares.length ∧
  (∀ col, 1 ≤ col ∧ col ≤ n → result ≤ count_occurrences squares col) ∧
  (∃ col, 1 ≤ col ∧ col ≤ n ∧ result = count_occurrences squares col)

@[reducible, simp]
def solve_precond (n : Int) (m : Int) (squares : List Int) : Prop :=
  ValidInput n m squares
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (m : Int) (squares : List Int) (h_precond : solve_precond n m squares) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (m : Int) (squares : List Int) (result : Int) (h_precond : solve_precond n m squares) : Prop :=
  CorrectResult n squares result

theorem solve_spec_satisfied (n : Int) (m : Int) (squares : List Int) (h_precond : solve_precond n m squares) :
    solve_postcond n m squares (solve n m squares h_precond) h_precond := by
  sorry
-- </vc-theorems>