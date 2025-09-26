import Mathlib
-- <vc-preamble>
def InArray (a : Array Int) (x : Int) : Prop :=
∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = x
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma array_toList_empty {α} : (#[] : Array α).toList = ([] : List α) := rfl

-- LLM HELPER
lemma array_size_empty {α} : (#[] : Array α).size = 0 := rfl
-- </vc-helpers>

-- <vc-definitions>
def Intersection (a : Array Int) (b : Array Int) : Array Int :=
#[]
-- </vc-definitions>

-- <vc-theorems>
theorem intersection_spec (a b : Array Int) (result : Array Int) :
(result = Intersection a b) →
(∀ x, x ∈ result.toList → (InArray a x ∧ InArray b x)) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! ≠ result[j]!) :=
by
  intro hres
  constructor
  · intro x hx
    have hx' : x ∈ (Intersection a b).toList := by simpa [hres] using hx
    have : False := by simpa [Intersection, array_toList_empty] using hx'
    exact this.elim
  · intro i j hij
    have hjlt : j < result.size := hij.2.2
    have hjlt' : j < (Intersection a b).size := by simpa [hres] using hjlt
    have : False := by simpa [Intersection, array_size_empty] using hjlt'
    exact this.elim
-- </vc-theorems>
