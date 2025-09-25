-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindEvenNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindEvenNumbers_spec (arr : Array Int) (evenNumbers : Array Int)
(h : evenNumbers = FindEvenNumbers arr) :
(∀ x, x ∈ arr.toList ∧ x % 2 = 0 → x ∈ evenNumbers.toList) ∧
(∀ x, x ∉ arr.toList → x ∉ evenNumbers.toList) ∧
(∀ k, 0 ≤ k ∧ k < evenNumbers.size → evenNumbers[k]! % 2 = 0) ∧
(∀ k l, 0 ≤ k ∧ k < l ∧ l < evenNumbers.size →
∃ n m, 0 ≤ n ∧ n < m ∧ m < arr.size ∧
evenNumbers[k]! = arr[n]! ∧
evenNumbers[l]! = arr[m]!) :=
sorry
-- </vc-theorems>