-- <vc-preamble>
@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- </vc-helpers>

-- <vc-definitions>
def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)

theorem findEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>