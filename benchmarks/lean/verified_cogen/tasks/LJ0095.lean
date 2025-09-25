-- <vc-preamble>
@[reducible, simp]
def containsConsecutiveNumbers_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ (∀ i, i < arr.size → 0 ≤ arr[i]! + 1 ∧ arr[i]! + 1 < 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsConsecutiveNumbers (arr : Array Int) (h_precond : containsConsecutiveNumbers_precond arr) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsConsecutiveNumbers_postcond (arr : Array Int) (is_consecutive : Bool) (h_precond : containsConsecutiveNumbers_precond arr) : Prop :=
  is_consecutive = (∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size ∧ j = i + 1 → arr[i]! + 1 = arr[j]!)

theorem containsConsecutiveNumbers_spec_satisfied (arr : Array Int) (h_precond : containsConsecutiveNumbers_precond arr) :
    containsConsecutiveNumbers_postcond arr (containsConsecutiveNumbers arr h_precond) h_precond := by
  sorry
-- </vc-theorems>