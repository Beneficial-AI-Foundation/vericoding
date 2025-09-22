-- <vc-preamble>
/- No preconditions required for this function -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasOnlyOneDistinctElement (a : Array Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) :=
  (result → (∀ i j, i < a.size → j < a.size → a[i]! = a[j]!)) ∧
  (¬result → (∃ i j, i < a.size ∧ j < a.size ∧ a[i]! ≠ a[j]!))

theorem hasOnlyOneDistinctElement_spec_satisfied (a: Array Int) :
    hasOnlyOneDistinctElement_postcond (a) (hasOnlyOneDistinctElement (a)) := by
  sorry
-- </vc-theorems>