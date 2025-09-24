-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (circle : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BinarySearch_spec (a : Array Int) (circle : Int) :
(∀ i, 1 ≤ i ∧ i < a.size → a[(i-1)]! < a[i]!) →
(∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! < a[j]!) →
let n := BinarySearch a circle
(0 ≤ n ∧ n ≤ a.size) ∧
(∀ i, 0 ≤ i ∧ i < n → a[i.toNat]! < circle) ∧
(∀ i, n ≤ i ∧ i < a.size → circle ≤ a[i.toNat]!) :=
sorry
-- </vc-theorems>