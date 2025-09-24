-- <vc-preamble>
@[reducible, simp]
def isOddAtOddIndex_precond (arr : Array Nat) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isOddAtOddIndex (arr : Array Nat) (h_precond : isOddAtOddIndex_precond arr) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isOddAtOddIndex_postcond (arr : Array Nat) (result: Bool) (h_precond : isOddAtOddIndex_precond arr) :=
  (∀ i, i < arr.size → (i % 2 = arr[i]! % 2)) ↔ result

theorem isOddAtOddIndex_spec_satisfied (arr: Array Nat) (h_precond : isOddAtOddIndex_precond arr) :
    isOddAtOddIndex_postcond arr (isOddAtOddIndex arr h_precond) h_precond := by
  sorry
-- </vc-theorems>