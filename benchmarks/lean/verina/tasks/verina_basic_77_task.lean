-- <vc-preamble>
@[reducible, simp]
def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size
-- </vc-preamble>

-- <vc-helpers>
def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val
-- </vc-helpers>

-- <vc-definitions>
def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def modify_array_element_postcond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result: Array (Array Nat)) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :=
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)

theorem modify_array_element_spec_satisfied (arr: Array (Array Nat)) (index1: Nat) (index2: Nat) (val: Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    modify_array_element_postcond (arr) (index1) (index2) (val) (modify_array_element (arr) (index1) (index2) (val) h_precond) h_precond := by
  sorry
-- </vc-theorems>