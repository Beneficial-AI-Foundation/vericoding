-- <vc-preamble>
@[reducible, simp]
def removeDuplicates_precond (a : Array Int) := a.size ≥ 1

def inArray (a : Array Int) (x : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeDuplicates (a : Array Int) (h_precond : removeDuplicates_precond a) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeDuplicates_postcond (a : Array Int) (result: Array Int) (h_precond : removeDuplicates_precond a) :=
  (∀ i, i < result.size → inArray a result[i]!) ∧ 
  (∀ i j, i < j → j < result.size → result[i]! ≠ result[j]!)

theorem removeDuplicates_spec_satisfied (a: Array Int) (h_precond : removeDuplicates_precond a) :
    removeDuplicates_postcond a (removeDuplicates a h_precond) h_precond := by
  sorry
-- </vc-theorems>