-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindEvenNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindEvenNumbers_spec (arr : Array Int) (evenNumbers : Array Int) :
(evenNumbers = FindEvenNumbers arr) →
(∀ x, (arr.contains x ∧ IsEven x) → evenNumbers.contains x) ∧
(∀ x, ¬arr.contains x → ¬evenNumbers.contains x) ∧
(∀ k l, 0 ≤ k ∧ k < l ∧ l < evenNumbers.size →
∃ n m, 0 ≤ n ∧ n < m ∧ m < arr.size ∧
evenNumbers[k]! = arr[n]! ∧ evenNumbers[l]! = arr[m]!) :=
sorry
-- </vc-theorems>