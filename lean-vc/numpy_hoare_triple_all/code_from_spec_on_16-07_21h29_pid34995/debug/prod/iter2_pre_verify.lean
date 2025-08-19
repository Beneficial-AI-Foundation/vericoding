import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.prod: Return the product of array elements over a given axis.
    
    Computes the product of all elements in the vector. For empty vectors,
    returns 1 as the identity element of multiplication.
    
    This is a reduction operation that applies multiplication across all
    elements to produce a single scalar result.
    
    Mathematical Properties:
    - Commutative: order of elements doesn't affect the final product
    - Associative: grouping of operations doesn't affect the result
    - Identity element: empty array product is 1
    - Contains zero: if any element is zero, the product is zero
-/
def prod {n : Nat} (a : Vector Float n) : Id Float :=
  pure (a.toList.foldl (· * ·) 1)

-- LLM HELPER
lemma vector_zero_elem_implies_foldl_zero {n : Nat} (a : Vector Float n) (i : Fin n) :
  a.get i = 0 → a.toList.foldl (· * ·) 1 = 0 := by
  intro h
  have : 0 ∈ a.toList := by
    rw [Vector.mem_toList]
    use i
    exact h
  exact List.foldl_mul_eq_zero_of_mem this

-- LLM HELPER
lemma vector_empty_implies_foldl_one {a : Vector Float 0} :
  a.toList.foldl (· * ·) 1 = 1 := by
  simp [Vector.toList_eq_nil_iff]

-- LLM HELPER
lemma List.foldl_mul_eq_zero_of_mem {l : List Float} (h : 0 ∈ l) :
  l.foldl (· * ·) 1 = 0 := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.mem_cons] at h
    cases h with
    | inl h_eq => 
      simp [List.foldl_cons, h_eq]
    | inr h_mem =>
      simp [List.foldl_cons]
      rw [ih h_mem]
      ring

/-- Specification: prod computes the product of all elements in a vector.
    
    The product operation has several important mathematical properties:
    1. For empty vectors, returns 1 (multiplicative identity)
    2. For non-empty vectors, returns the product of all elements
    3. If any element is zero, the result is zero
    4. The operation is commutative and associative
    
    This specification captures both the basic behavior and key mathematical
    properties that make prod well-defined and predictable.
-/
theorem prod_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    prod a
    ⦃⇓result => ⌜result = (a.toList.foldl (· * ·) 1) ∧ 
                 (n = 0 → result = 1) ∧
                 (∃ i : Fin n, a.get i = 0) → result = 0⌝⦄ := by
  rw [prod]
  apply do_pure
  constructor
  · rfl
  constructor
  · intro h
    cases n with
    | zero => 
      simp [Vector.toList_eq_nil_iff] at h ⊢
    | succ n' =>
      contradiction
  · intro ⟨i, hi⟩
    exact vector_zero_elem_implies_foldl_zero a i hi