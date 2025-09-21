-- <vc-preamble>
@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSorted_postcond (a : Array Int) (result: Bool) (h_precond : isSorted_precond (a)) :=
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result

theorem isSorted_spec_satisfied (a: Array Int) (h_precond : isSorted_precond (a)) :
    isSorted_postcond (a) (isSorted (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>