import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.array_equal: True if two arrays have the same shape and elements, False otherwise.

    Compares two arrays element-wise and returns a single boolean value indicating
    whether the arrays are completely equal. Unlike element-wise comparison functions,
    this returns a single boolean result for the entire comparison.
    
    The function returns True if and only if:
    1. The arrays have the same shape (enforced by Vector type system)
    2. All corresponding elements are equal
    
    For Vector types, the shape constraint is automatically satisfied by the type system,
    so we only need to check element-wise equality.
-/
def arrayEqual {T : Type} [BEq T] {n : Nat} (a1 a2 : Vector T n) : Id Bool :=
  pure (a1 == a2)

-- LLM HELPER
lemma vector_eq_iff_get_eq {T : Type} [BEq T] {n : Nat} (a1 a2 : Vector T n) :
    (a1 == a2) = true ↔ ∀ i : Fin n, (a1.get i == a2.get i) = true := by
  constructor
  · intro h
    intro i
    have h_eq : a1 = a2 := by
      rw [← BEq.beq_eq_true] at h
      exact h
    rw [h_eq]
    simp
  · intro h
    rw [BEq.beq_eq_true]
    rw [Vector.ext_iff]
    intro i
    have := h i
    rw [BEq.beq_eq_true] at this
    exact this

-- LLM HELPER
lemma exists_neq_imp_false {T : Type} [BEq T] {n : Nat} (a1 a2 : Vector T n) :
    (∃ i : Fin n, ¬(a1.get i == a2.get i) = true) → (a1 == a2) = false := by
  intro h
  cases' h with i hi
  rw [BEq.beq_eq_false]
  intro h_eq
  rw [h_eq] at hi
  simp at hi

/-- Specification: numpy.array_equal returns True if and only if all corresponding 
    elements in the two vectors are equal.

    Precondition: True (vectors have the same length by the type system)
    Postcondition: The result is True if and only if all corresponding elements are equal
    
    Mathematical properties:
    - Array equality is reflexive: arrayEqual(a, a) = True for any array a
    - Array equality is symmetric: arrayEqual(a, b) = arrayEqual(b, a)
    - Array equality is transitive: if arrayEqual(a, b) and arrayEqual(b, c), then arrayEqual(a, c)
    - Empty arrays are equal: arrayEqual([], []) = True (vacuous truth)
    - arrayEqual(a, b) = all(elementwise_equal(a, b)) - equivalent to checking all elements are equal
    
    Sanity checks:
    - For empty vectors (n = 0), the result is True by vacuous truth
    - For single element vectors [x] and [y], result is True iff x == y
    - For identical vectors, result is True
    - For vectors differing in any element, result is False
    - arrayEqual is the logical AND of all element-wise comparisons
-/
theorem arrayEqual_spec {T : Type} [BEq T] {n : Nat} (a1 a2 : Vector T n) :
    ⦃⌜True⌝⦄
    arrayEqual a1 a2
    ⦃⇓result => ⌜(result = true ↔ ∀ i : Fin n, (a1.get i == a2.get i) = true) ∧
                  (n = 0 → result = true) ∧
                  (∃ i : Fin n, ¬(a1.get i == a2.get i) = true → result = false)⌝⦄ := by
  unfold arrayEqual
  simp [hs_pure]
  constructor
  · constructor
    · exact vector_eq_iff_get_eq a1 a2
    · constructor
      · intro h
        cases' n with
        | zero => simp
        | succ n' => simp at h
      · intro h
        exact exists_neq_imp_false a1 a2 h
  · simp