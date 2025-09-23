-- <vc-preamble>
def InArray (a : Array Int) (x : Int) : Prop :=
∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DissimilarElements (a b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem DissimilarElements_spec (a b : Array Int) (result : Array Int) :

-- All elements in result are in exactly one of a or b (XOR)

(∀ x, x ∈ result.toList → (InArray a x ≠ InArray b x)) ∧

-- All elements in result are unique

(∀ i j, 0 ≤ i → i < j → j < result.size → result[i]! ≠ result[j]!) :=
sorry
-- </vc-theorems>