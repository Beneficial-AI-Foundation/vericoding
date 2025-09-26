-- <vc-preamble>
@[reducible, simp]
def binarySearch_precond (arr : Array Int) (target : Int) : Prop :=
  ∀ i j, i < j → j < arr.size → arr[i]! ≤ arr[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (arr : Array Int) (target : Int) (h_precond : binarySearch_precond arr target) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def binarySearch_postcond (arr : Array Int) (target : Int) (result : Option Nat) (h_precond : binarySearch_precond arr target) : Prop :=
  match result with
  | some index => arr[index]! = target ∧ arr.size > 0 ∧ index < arr.size
  | none => ∀ i, i < arr.size → arr[i]! ≠ target

theorem binarySearch_spec_satisfied (arr : Array Int) (target : Int) (h_precond : binarySearch_precond arr target) :
    binarySearch_postcond arr target (binarySearch arr target h_precond) h_precond := by
  sorry
-- </vc-theorems>