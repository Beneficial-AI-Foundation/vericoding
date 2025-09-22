-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (key : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BinarySearch_spec (a : Array Int) (key : Int) (n : Int) :
(∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!) →
(0 ≤ n ∧ n ≤ a.size) ∧
(∀ i, 0 ≤ i ∧ i < n → a[i.toNat]! < key) ∧
(n = a.size → ∀ i, 0 ≤ i ∧ i < a.size →  a[i]!  < key) ∧
(∀ i, n ≤ i ∧ i < a.size → a[i.toNat]!  ≥ key) :=
sorry
-- </vc-theorems>