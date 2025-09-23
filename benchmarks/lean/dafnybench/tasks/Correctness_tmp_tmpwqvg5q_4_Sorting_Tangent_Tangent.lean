-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (circle : Int) : Int :=
sorry

def Tangent (r : Array Int) (x : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BinarySearch_spec (a : Array Int) (circle : Int) (n : Int) :
(∀ i, 1 ≤ i ∧ i < a.size → a[(i-1)]! < a[i]!) →
(∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! < a[j]!) →
0 ≤ n ∧ n ≤ a.size ∧
(∀ i, 0 ≤ i ∧ i < n → a[i.toNat]! < circle) ∧
(∀ i, n ≤ i ∧ i < a.size → circle ≤ a[i.toNat]!) :=
sorry

theorem Tangent_spec (r x : Array Int) (found : Bool) :
(∀ i, 1 ≤ i ∧ i < x.size → x[(i-1)]! < x[i]!) →
(∀ i j, 0 ≤ i ∧ i < j ∧ j < x.size → x[i]! < x[j]!) →
(¬found →
(∀ i j, 0 ≤ i ∧ i < r.size ∧ 0 ≤ j ∧ j < x.size → r[i]! ≠ x[j]!)) ∧
(found →
(∃ i j, 0 ≤ i ∧ i < r.size ∧ 0 ≤ j ∧ j < x.size ∧ r[i]! = x[j]!)) :=
sorry
-- </vc-theorems>