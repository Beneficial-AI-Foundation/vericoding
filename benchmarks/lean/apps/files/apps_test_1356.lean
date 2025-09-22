-- <vc-preamble>
def count_a (s : List Char) : Int :=
  match s with
  | [] => 0
  | c :: cs => (if c = 'a' then 1 else 0) + count_a cs

def my_min (a b : Int) : Int :=
  if a ≤ b then a else b

def ValidInput (s : List Char) : Prop :=
  s.length ≥ 1 ∧ ∃ i, 0 ≤ i ∧ i < s.length ∧ s.get! i = 'a'

def IsGoodString (s : List Char) : Prop :=
  s.length > 0 ∧ count_a s > s.length / 2

@[reducible, simp]
def solve_precond (s : List Char) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : List Char) (h_precond : solve_precond s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : List Char) (result : Int) (h_precond : solve_precond s) : Prop :=
  result ≥ 1 ∧ result ≤ s.length ∧ result = my_min (2 * count_a s - 1) s.length

theorem solve_spec_satisfied (s : List Char) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>