-- <vc-preamble>
def isEven (n : Int) : Bool :=
n % 2 == 0

def isOdd (n : Int) : Bool :=
n % 2 != 0

@[reducible, simp]
def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def firstEvenOddDifference_postcond (a : Array Int) (result: Int) (h_precond : firstEvenOddDifference_precond (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))

theorem firstEvenOddDifference_spec_satisfied (a: Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    firstEvenOddDifference_postcond (a) (firstEvenOddDifference (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>