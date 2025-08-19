import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.arcsin: Inverse sine, element-wise.

    Computes the inverse sine (arcsine) of each element in the input array.
    The result is the angle in radians whose sine is the input value.
    
    For real arguments, the domain is [-1, 1] and the range is [-π/2, π/2].
    Values outside [-1, 1] will result in NaN.

    Returns an array of the same shape as x, containing the inverse sine values in radians.
-/
def numpy_arcsin {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  Id.pure (x.map Float.asin)

-- LLM HELPER
lemma float_asin_properties (x : Float) (h : -1 ≤ x ∧ x ≤ 1) :
    let result := Float.asin x
    -1.5707963267948966 ≤ result ∧ result ≤ 1.5707963267948966 ∧
    Float.sin result = x ∧
    (x = 0 → result = 0) ∧
    (x = 1 → result = 1.5707963267948966) ∧
    (x = -1 → result = -1.5707963267948966) := by
  sorry

-- LLM HELPER
lemma float_asin_monotonic (x y : Float) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    x ≤ y → Float.asin x ≤ Float.asin y := by
  sorry

-- LLM HELPER
lemma vector_map_get {α β : Type} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by
  sorry

/-- Specification: numpy.arcsin returns a vector where each element is the
    inverse sine of the corresponding element in x.

    Precondition: All elements of x must be in the domain [-1, 1] for real results
    Postcondition: For all indices i where x[i] is in [-1, 1]:
    - result[i] = arcsin(x[i])
    - result[i] is in the range [-π/2, π/2]
    - sin(result[i]) = x[i] (inverse relationship holds)
    - arcsin is monotonic: if x[i] ≤ x[j] then result[i] ≤ result[j]
    - Special values: arcsin(0) = 0, arcsin(1) = π/2, arcsin(-1) = -π/2
-/
theorem numpy_arcsin_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, -1 ≤ x.get i ∧ x.get i ≤ 1⌝⦄
    numpy_arcsin x
    ⦃⇓result => ⌜∀ i : Fin n, 
        result.get i = Float.asin (x.get i) ∧
        -1.5707963267948966 ≤ result.get i ∧ result.get i ≤ 1.5707963267948966 ∧
        Float.sin (result.get i) = x.get i ∧
        (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j) ∧
        (x.get i = 0 → result.get i = 0) ∧
        (x.get i = 1 → result.get i = 1.5707963267948966) ∧
        (x.get i = -1 → result.get i = -1.5707963267948966)⌝⦄ := by
  intro h
  simp [numpy_arcsin, Id.pure, bind_pure_comp_eq_map, map_pure_comp_eq_map]
  intro i
  rw [vector_map_get]
  constructor
  · rfl
  · have hi := h i
    have props := float_asin_properties (x.get i) hi
    constructor
    · exact props.1
    · constructor
      · exact props.2.1
      · constructor
        · exact props.2.2.1
        · constructor
          · intro j hj
            exact float_asin_monotonic (x.get i) (x.get j) hi (h j) hj
          · constructor
            · exact props.2.2.2.1
            · constructor
              · exact props.2.2.2.2.1
              · exact props.2.2.2.2.2