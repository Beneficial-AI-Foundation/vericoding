-- <vc-preamble>
@[reducible, simp]
def uniqueBetter_precond (a : Array Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueBetter (a : Array Int) (h_precond : uniqueBetter_precond a) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def uniqueBetter_postcond (a : Array Int) (result: Array Int) (h_precond : uniqueBetter_precond a) :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! < result[j]!

theorem uniqueBetter_spec_satisfied (a: Array Int) (h_precond : uniqueBetter_precond a) :
    uniqueBetter_postcond a (uniqueBetter a h_precond) h_precond := by
  sorry
-- </vc-theorems>