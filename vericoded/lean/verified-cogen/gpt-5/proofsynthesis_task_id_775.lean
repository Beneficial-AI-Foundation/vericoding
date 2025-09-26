import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isOddAtOddIndex_precond (arr : Array Nat) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Generic bridge between a proposition and its boolean decision
theorem iff_decide {p : Prop} [Decidable p] : p ↔ (decide p = true) := by
  by_cases h : p
  · simp [h]
  · simp [h]

-- </vc-helpers>

-- <vc-definitions>
def isOddAtOddIndex (arr : Array Nat) (h_precond : isOddAtOddIndex_precond arr) : Bool :=
  decide (∀ i, i < arr.size → (i % 2 = arr[i]! % 2))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isOddAtOddIndex_postcond (arr : Array Nat) (result: Bool) (h_precond : isOddAtOddIndex_precond arr) :=
  (∀ i, i < arr.size → (i % 2 = arr[i]! % 2)) ↔ result

theorem isOddAtOddIndex_spec_satisfied (arr: Array Nat) (h_precond : isOddAtOddIndex_precond arr) :
    isOddAtOddIndex_postcond arr (isOddAtOddIndex arr h_precond) h_precond := by
    classical
  unfold isOddAtOddIndex_postcond isOddAtOddIndex
  by_cases h : ∀ i, i < arr.size → (i % 2 = arr[i]! % 2)
  · simp [h]
  · simp [h]

-- </vc-theorems>
