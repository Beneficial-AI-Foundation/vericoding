-- <vc-preamble>
def InArray (a : Array Int) (x : Int) : Prop :=
∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Intersection (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem intersection_spec (a b : Array Int) (result : Array Int) :
(result = Intersection a b) →
(∀ x, x ∈ result.toList → (InArray a x ∧ InArray b x)) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! ≠ result[j]!) :=
sorry
-- </vc-theorems>