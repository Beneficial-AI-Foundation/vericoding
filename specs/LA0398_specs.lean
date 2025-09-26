-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def MaxCoders (n : Int) : Int :=
  n * n / 2 + n * n % 2

def IntToString (x : Int) : String := toString x

def ValidOutputFormat (result : List String) (n : Int) : Prop :=
  result.length = n.natAbs + 1 ∧
  result[0]! = IntToString (MaxCoders n) ∧
  (∀ i, 1 ≤ i ∧ i ≤ n → (result[i.natAbs]!).length = n.natAbs)

def ValidCheckerboardPlacement (result : List String) (n : Int) : Prop :=
  ∀ i, 1 ≤ i ∧ i ≤ n → ∀ j, 0 ≤ j ∧ j < n →
    ((result[i.natAbs]!).data[j.natAbs]! = 'C' ↔ 
      (if (i - 1) % 2 = 0 then j % 2 = 0 else j % 2 = 1))

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List String) (h_precond : solve_precond n) : Prop :=
  ValidOutputFormat result n ∧ ValidCheckerboardPlacement result n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>