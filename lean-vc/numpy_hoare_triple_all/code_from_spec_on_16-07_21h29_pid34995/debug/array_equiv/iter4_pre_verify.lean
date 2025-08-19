import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.array_equiv: Returns True if input arrays are shape consistent and all elements equal.

    Shape consistent means they are either the same shape, or one input array
    can be broadcasted to create the same shape as the other one.
    
    For 1D arrays of the same size, this means element-wise comparison.
    The function returns True if all corresponding elements are equal.
-/
def array_equiv {n : Nat} (a1 a2 : Vector Float n) : Id Bool :=
  pure (decide (∀ i : Fin n, a1.get i = a2.get i))

-- LLM HELPER
lemma decidable_forall_fin_eq {n : Nat} (a1 a2 : Vector Float n) : 
  Decidable (∀ i : Fin n, a1.get i = a2.get i) := by
  induction n with
  | zero => 
    simp only [Fin.eq_iff_veq]
    exact decidableTrue
  | succ n ih =>
    have : (∀ i : Fin (n + 1), a1.get i = a2.get i) ↔ 
           (a1.get 0 = a2.get 0 ∧ ∀ i : Fin n, a1.get i.succ = a2.get i.succ) := by
      constructor
      · intro h
        constructor
        · exact h 0
        · intro i
          exact h i.succ
      · intro ⟨h0, h_succ⟩ i
        cases' Fin.eq_zero_or_eq_succ i with h h
        · rw [h]; exact h0
        · obtain ⟨j, rfl⟩ := h
          exact h_succ j
    rw [this]
    exact And.decidable

-- LLM HELPER
instance {n : Nat} (a1 a2 : Vector Float n) : Decidable (∀ i : Fin n, a1.get i = a2.get i) :=
  decidable_forall_fin_eq a1 a2

/-- Specification: array_equiv returns true iff all corresponding elements are equal.

    Precondition: True (works for any two vectors of the same size)
    Postcondition: result = true iff all elements at corresponding indices are equal
    
    Mathematical properties satisfied:
    - Reflexivity: array_equiv a a = true (any array is equivalent to itself)
    - Symmetry: array_equiv a b = array_equiv b a (equivalence is symmetric)
    - Element-wise equality: result = true iff ∀ i, a1[i] = a2[i]
    - Empty array handling: for n=0, the result is vacuously true
    - Finite precision: uses Float equality (may have precision limitations)
-/
theorem array_equiv_spec {n : Nat} (a1 a2 : Vector Float n) :
    ⦃⌜True⌝⦄
    array_equiv a1 a2
    ⦃⇓result => ⌜result = (∀ i : Fin n, a1.get i = a2.get i)⌝⦄ := by
  simp only [array_equiv]
  apply pure_spec
  simp [decide_eq_true_iff]