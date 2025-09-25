-- <vc-preamble>
@[reducible, simp]
def isEvenAtEvenIndex_precond (arr : Array Nat) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isEvenAtEvenIndex (arr : Array Nat) (h_precond : isEvenAtEvenIndex_precond (arr)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isEvenAtEvenIndex_postcond (arr : Array Nat) (result: Bool) (h_precond : isEvenAtEvenIndex_precond (arr)) :=
  (∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2))) ↔ result

theorem isEvenAtEvenIndex_spec_satisfied (arr: Array Nat) (h_precond : isEvenAtEvenIndex_precond (arr)) :
    isEvenAtEvenIndex_postcond (arr) (isEvenAtEvenIndex (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>