-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0
def IsOdd (n : Int) : Bool :=
n % 2 ≠ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FirstEvenOddDifference (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FirstEvenOddDifference_spec (a : Array Int) :
a.size ≥ 2 →
(∃ i, 0 ≤ i ∧ i < a.size ∧ IsEven (a[i]!)) →
(∃ i, 0 ≤ i ∧ i < a.size ∧ IsOdd (a[i]!)) →
∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size ∧
IsEven (a[i]!) ∧ IsOdd (a[j]!) ∧
FirstEvenOddDifference a = a[i]! - a[j]! ∧
(∀ k, 0 ≤ k ∧ k < i → IsOdd (a[k]!)) ∧
(∀ k, 0 ≤ k ∧ k < j → IsEven (a[k]!)) :=
sorry
-- </vc-theorems>