-- <vc-preamble>
def seq_min (s : List Int) : Int :=
  if h : s.length > 0 then
    if s.length = 1 then s[0]!
    else if s[0]! ≤ seq_min s.tail then s[0]!
    else seq_min s.tail
  else 0

def ValidInput (arr : List Int) : Prop :=
  arr.length ≥ 2 ∧ 
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < arr.length ∧ arr[i]! = arr[j]! ∧ arr[i]! = seq_min arr

@[reducible, simp]
def solve_precond (arr : List Int) : Prop :=
  ValidInput arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) (h_precond : solve_precond arr) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (arr : List Int) (result: Int) (h_precond : solve_precond arr) : Prop :=
  result > 0 ∧
  result ≤ arr.length - 1 ∧
  (∃ i j, 0 ≤ i ∧ i < j ∧ j < arr.length ∧ arr[i]! = arr[j]! ∧ arr[i]! = seq_min arr ∧ j - i = result) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.length ∧ arr[i]! = arr[j]! ∧ arr[i]! = seq_min arr → j - i ≥ result)

theorem solve_spec_satisfied (arr : List Int) (h_precond : solve_precond arr) :
    solve_postcond arr (solve arr h_precond) h_precond := by
  sorry
-- </vc-theorems>