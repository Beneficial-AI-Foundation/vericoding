import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def allEqual {T : Type} [BEq T] {n : Nat} (actual desired : Vector T n) : Bool :=
  (List.range n).all (fun i => 
    if h : i < n then
      actual.get ⟨i, h⟩ == desired.get ⟨i, h⟩
    else
      true)

/-- numpy.testing.assert_array_equal: Checks if two arrays are equal

    This function tests whether two arrays have the same shape and all elements
    are equal. In NumPy, this function raises an AssertionError if the arrays
    are not equal, but in our Lean specification, we model it as returning
    a boolean value indicating whether the assertion would pass.
    
    The function checks:
    1. Shape equality (automatically satisfied by Vector type system)
    2. Element-wise equality using strict equality (==)
    
    Unlike numpy.array_equal, this function is specifically designed for testing
    and assertion purposes. It's more strict about equality and is meant to be
    used in test suites to verify array contents.
    
    For Vector types, the shape constraint is automatically satisfied by the type system,
    so we focus on element-wise equality verification.
-/
def assertArrayEqual {T : Type} [BEq T] {n : Nat} (actual desired : Vector T n) : Id Bool :=
  do
    let mut result := true
    for i in [0:n] do
      if h : i < n then
        if !(actual.get ⟨i, h⟩ == desired.get ⟨i, h⟩) then
          result := false
          break
    return result

/-- Specification: numpy.testing.assert_array_equal returns True if and only if
    all corresponding elements in the two vectors are equal.

    Precondition: True (vectors have the same length by the type system)
    Postcondition: The result is True if and only if all corresponding elements are equal
    
    Mathematical properties:
    - Assertion equality is reflexive: assertArrayEqual(a, a) = True for any array a
    - Assertion equality is symmetric: assertArrayEqual(a, b) = assertArrayEqual(b, a)
    - Assertion equality is transitive: if assertArrayEqual(a, b) and assertArrayEqual(b, c), then assertArrayEqual(a, c)
    - Empty arrays pass assertion: assertArrayEqual([], []) = True (vacuous truth)
    - assertArrayEqual(a, b) = all(elementwise_equal(a, b)) - equivalent to checking all elements are equal
    - The function is deterministic: same inputs always produce same result
    - The function is total: defined for all valid vector inputs
    
    Sanity checks:
    - For empty vectors (n = 0), the result is True by vacuous truth
    - For single element vectors [x] and [y], result is True iff x == y
    - For identical vectors, result is True
    - For vectors differing in any element, result is False
    - assertArrayEqual is the logical AND of all element-wise comparisons
    - The assertion succeeds if and only if the vectors are element-wise equal
    - Performance: O(n) time complexity, where n is the vector length
    - The function short-circuits on first inequality found (implementation detail)
-/
theorem assertArrayEqual_spec {T : Type} [BEq T] {n : Nat} (actual desired : Vector T n) :
    ⦃⌜True⌝⦄
    assertArrayEqual actual desired
    ⦃⇓result => ⌜(result = true ↔ ∀ i : Fin n, actual.get i == desired.get i) ∧
                  (n = 0 → result = true) ∧
                  (∃ i : Fin n, ¬(actual.get i == desired.get i) → result = false) ∧
                  (result = true → ∀ i : Fin n, actual.get i == desired.get i) ∧
                  (result = false → ∃ i : Fin n, ¬(actual.get i == desired.get i))⌝⦄ := by
  unfold assertArrayEqual
  apply WP.do_rule
  · simp
  · intro result
    apply WP.for_rule
    · simp
    · intro i hi
      simp at hi
      by_cases h : actual.get ⟨i, hi⟩ == desired.get ⟨i, hi⟩
      · simp [h]
        apply WP.pure_rule
        simp
      · simp [h]
        apply WP.if_rule
        · simp
        · apply WP.pure_rule
          simp
        · apply WP.pure_rule
          simp
    · intro final_result
      apply WP.pure_rule
      simp
      constructor
      · constructor
        · intro h
          by_contra h'
          simp at h'
          obtain ⟨i, hi⟩ := h'
          cases n with
          | zero => simp at hi
          | succ n' => 
            have : i.val < n := i.isLt
            rw [h] at final_result
            simp at final_result
        · intro h
          cases n with
          | zero => simp
          | succ n' => 
            rw [h]
            simp
      · constructor
        · intro h
          by_cases hn : n = 0
          · simp [hn]
          · cases n with
            | zero => contradiction
            | succ n' => simp
        · constructor
          · intro h
            cases n with
            | zero => simp
            | succ n' => 
              by_contra h'
              simp at h'
              obtain ⟨i, hi⟩ := h'
              rw [h] at final_result
              simp at final_result
          · constructor
            · intro h
              by_contra h'
              simp at h'
              obtain ⟨i, hi⟩ := h'
              rw [h] at final_result
              simp at final_result
            · intro h
              cases n with
              | zero => simp at h
              | succ n' => 
                by_contra h'
                simp at h'
                rw [h'] at final_result
                simp at final_result
                obtain ⟨i, hi⟩ := h
                simp at final_result