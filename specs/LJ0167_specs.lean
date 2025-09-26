-- <vc-preamble>
@[reducible, simp]
def unique_precond (a : Array Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique (a : Array Int) (h_precond : unique_precond a) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def unique_postcond (a : Array Int) (result: Array Int) (h_precond : unique_precond a) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! < result[j]!

theorem unique_spec_satisfied (a : Array Int) (h_precond : unique_precond a) :
    unique_postcond a (unique a h_precond) h_precond := by
  sorry
-- </vc-theorems>