-- <vc-preamble>
@[reducible, simp]
def elementWiseDivide_precond (arr1 : Array Nat) (arr2 : Array Nat) :=
  arr1.size = arr2.size ∧ 
  (∀ i, i < arr2.size → arr2[i]! ≠ 0) ∧
  (∀ i, i < arr1.size → (arr1[i]! / arr2[i]! : Int) ≥ Int.negSucc 2147483647 ∧ (arr1[i]! / arr2[i]! : Int) ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elementWiseDivide (arr1 : Array Nat) (arr2 : Array Nat) (h_precond : elementWiseDivide_precond arr1 arr2) : Array Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def elementWiseDivide_postcond (arr1 : Array Nat) (arr2 : Array Nat) (result: Array Nat) (h_precond : elementWiseDivide_precond arr1 arr2) :=
  result.size = arr1.size ∧ (∀ i, i < result.size → result[i]! = arr1[i]! / arr2[i]!)

theorem elementWiseDivide_spec_satisfied (arr1: Array Nat) (arr2: Array Nat) (h_precond : elementWiseDivide_precond arr1 arr2) :
    elementWiseDivide_postcond arr1 arr2 (elementWiseDivide arr1 arr2 h_precond) h_precond := by
  sorry
-- </vc-theorems>