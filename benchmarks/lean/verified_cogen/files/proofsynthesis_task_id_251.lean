-- <vc-preamble>
@[reducible, simp]
def insertBeforeEach_precond (arr : Array Int) (elem : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insertBeforeEach (arr : Array Int) (elem : Int) (h_precond : insertBeforeEach_precond (arr) (elem)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def insertBeforeEach_postcond (arr : Array Int) (elem : Int) (result : Array Int) (h_precond : insertBeforeEach_precond (arr) (elem)) : Prop :=
  result.size = (2 * arr.size) ∧ 
  (∀ k, k < arr.size → result[2 * k]! = elem) ∧
  (∀ k, k < arr.size → result[2 * k + 1]! = arr[k]!)

theorem insertBeforeEach_spec_satisfied (arr : Array Int) (elem : Int) (h_precond : insertBeforeEach_precond (arr) (elem)) :
    insertBeforeEach_postcond (arr) (elem) (insertBeforeEach (arr) (elem) h_precond) h_precond := by
  sorry
-- </vc-theorems>