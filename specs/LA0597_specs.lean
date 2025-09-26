-- <vc-preamble>
def ValidInput (n : Int) (a_1 a_2 : List Int) : Prop :=
  n ≥ 1 ∧
  a_1.length = n ∧ a_2.length = n ∧
  ∀ i, 0 ≤ i ∧ i < n → 1 ≤ a_1[i.natAbs]! ∧ a_1[i.natAbs]! ≤ 100 ∧ 1 ≤ a_2[i.natAbs]! ∧ a_2[i.natAbs]! ≤ 100

def sum_range (s : List Int) (start end_ : Int) : Int :=
  if start ≥ end_ then 0
  else (s.drop start.natAbs).take (end_ - start).natAbs |>.sum

def IsValidResult (n : Int) (a_1 a_2 : List Int) (result : Int) : Prop :=
  ValidInput n a_1 a_2 →
  result ≥ n + 1 ∧
  result ≤ (n + 1) * 100 ∧
  (∃ i, 0 ≤ i ∧ i < n ∧ result = sum_range a_1 0 (i + 1) + sum_range a_2 i n) ∧
  (∀ i, 0 ≤ i ∧ i < n → result ≥ sum_range a_1 0 (i + 1) + sum_range a_2 i n)

@[reducible, simp]
def solve_precond (n : Int) (a_1 a_2 : List Int) : Prop :=
  ValidInput n a_1 a_2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a_1 a_2 : List Int) (h_precond : solve_precond n a_1 a_2) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a_1 a_2 : List Int) (result : Int) (h_precond : solve_precond n a_1 a_2) : Prop :=
  IsValidResult n a_1 a_2 result

theorem solve_spec_satisfied (n : Int) (a_1 a_2 : List Int) (h_precond : solve_precond n a_1 a_2) :
    solve_postcond n a_1 a_2 (solve n a_1 a_2 h_precond) h_precond := by
  sorry
-- </vc-theorems>