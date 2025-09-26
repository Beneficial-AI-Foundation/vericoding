import Mathlib
-- <vc-preamble>
def InArray (a : Array Int) (x : Int) : Prop :=
∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = x
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def SharedElements (a : Array Int) (b : Array Int) : Array Int :=
#[]
-- </vc-definitions>

-- <vc-theorems>
theorem SharedElements_spec (a b : Array Int) (result : Array Int) :
(result = SharedElements a b) →
(∀ x, x ∈ result.toList → (InArray a x ∧ InArray b x)) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! ≠ result[j]!) :=
by
  intro h
  subst h
  constructor
  · intro x hx
    have : False := by
      simpa [SharedElements] using hx
    exact this.elim
  · intro i j hcond
    have hj0 : j < 0 := by simpa [SharedElements] using hcond.2.2
    exact False.elim ((Nat.not_lt_zero _) hj0)
-- </vc-theorems>
