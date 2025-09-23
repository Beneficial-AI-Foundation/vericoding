-- <vc-preamble>
@[reducible, simp]
def sharedElements_precond (list1 : Array Int) (list2 : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sharedElements (list1 : Array Int) (list2 : Array Int) (h_precond : sharedElements_precond (list1) (list2)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sharedElements_postcond (list1 : Array Int) (list2 : Array Int) (shared: Array Int) (h_precond : sharedElements_precond (list1) (list2)) :=
  (∀ i, i < shared.size → (list1.contains shared[i]! ∧ list2.contains shared[i]!)) ∧
  (∀ i j, i < j → j < shared.size → shared[i]! ≠ shared[j]!)

theorem sharedElements_spec_satisfied (list1: Array Int) (list2: Array Int) (h_precond : sharedElements_precond (list1) (list2)) :
    sharedElements_postcond (list1) (list2) (sharedElements (list1) (list2) h_precond) h_precond := by
  sorry
-- </vc-theorems>