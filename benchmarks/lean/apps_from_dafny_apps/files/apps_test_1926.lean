-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 2 ∧ a.length = n.natAbs

def CountViolationsForK (a : List Int) (n : Int) (k : Int) : Nat :=
  sorry

def ValidOutput (result : List Int) (n : Int) (a : List Int) : Prop :=
  result.length = (n - 1).natAbs ∧
  (∀ k, 1 ≤ k ∧ k ≤ n - 1 → ∃ v, result.get? (k.natAbs - 1) = some v ∧ v ≥ 0) ∧
  (∀ k, 1 ≤ k ∧ k ≤ n - 1 → ∃ v, result.get? (k.natAbs - 1) = some v ∧ v = CountViolationsForK a n k)

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : List Int) (h_precond : solve_precond n a) : Prop :=
  ValidOutput result n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>
