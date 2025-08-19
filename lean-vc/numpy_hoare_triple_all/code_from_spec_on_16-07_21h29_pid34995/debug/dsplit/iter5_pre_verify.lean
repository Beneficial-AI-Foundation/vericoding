import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def splitVectorHelper {n k : Nat} (arr : Vector Float (k * n)) (i : Nat) (hi : i < k) : Vector Float n :=
  Vector.ofFn (fun j => arr.get ⟨i * n + j.val, by
    have h2 : j.val < n := j.isLt
    have h3 : i < k := hi
    calc i * n + j.val
      < i * n + n := Nat.add_lt_add_left h2 _
      _ = (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h3)
  ⟩)

-- LLM HELPER
lemma mem_range_of_lt {k : Nat} {i : Nat} (h : i < k) : i ∈ List.range k :=
  List.mem_range.mpr h

/-- Split a 1D vector into equal sections (simplified version of dsplit).
    
    Since dsplit operates on the 3rd axis of 3D arrays, this simplified version
    demonstrates the splitting behavior on a 1D vector. The actual dsplit would
    work on nested Vector structures representing 3D arrays.
    
    This function divides a vector into k equal sections, where k must divide
    the length of the vector evenly. Returns a list of vectors.
-/
def dsplit {n k : Nat} (arr : Vector Float (k * n)) (sections : Nat) 
  (h : sections = k ∧ k > 0) : Id (List (Vector Float n)) :=
  pure (List.range k |>.map (fun i => splitVectorHelper arr i (by
    exact List.mem_range.mp (List.mem_range.mpr (Nat.lt_refl_of_pos (Nat.pos_of_ne_zero (fun h_eq => by
      have : k > 0 := h.2
      rw [h_eq] at this
      exact Nat.lt_irrefl 0 this))))
  )))

-- LLM HELPER
lemma list_length_range_map {α : Type*} (f : Nat → α) (k : Nat) : 
  (List.range k |>.map f).length = k :=
  List.length_map _ _

-- LLM HELPER
lemma get_splitVectorHelper {n k : Nat} (arr : Vector Float (k * n)) (i : Nat) (hi : i < k) (j : Fin n) :
  (splitVectorHelper arr i hi).get j = arr.get ⟨i * n + j.val, by
    have h2 : j.val < n := j.isLt
    have h3 : i < k := hi
    calc i * n + j.val
      < i * n + n := Nat.add_lt_add_left h2 _
      _ = (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h3)
  ⟩ := by
  simp [splitVectorHelper, Vector.get_ofFn]

-- LLM HELPER  
lemma range_map_membership {n k : Nat} (arr : Vector Float (k * n)) (i : Fin k) :
  ∃ sub, sub ∈ (List.range k |>.map (fun j => splitVectorHelper arr j (by
    have : j < k := by
      exact List.mem_range.mp (List.mem_range.mpr (Nat.lt_refl_of_pos (Nat.pos_of_ne_zero (fun h_eq => by
        have : k > 0 := Nat.pos_of_ne_zero (fun h_k_eq => by
          rw [h_k_eq] at i
          exact Nat.not_lt_zero i.val i.isLt)
        rw [h_eq] at this
        exact Nat.lt_irrefl 0 this))))
    exact this
  ))) ∧ ∀ (m : Fin n), sub.get m = arr.get ⟨i.val * n + m.val, by
    have h1 : i.val < k := i.isLt
    have h2 : m.val < n := m.isLt
    calc i.val * n + m.val
      < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
  ⟩ := by
  use splitVectorHelper arr i.val i.isLt
  constructor
  · simp [List.mem_map, List.mem_range]
    use i.val
    exact ⟨i.isLt, rfl⟩
  · intro m
    exact get_splitVectorHelper arr i.val i.isLt m

/-- Specification: dsplit divides a vector into equal sections.
    
    Precondition: sections = k and k > 0 (array size must be k * n)
    Postcondition: Returns k sub-vectors, each of size n. The i-th sub-vector
                   contains elements from positions i*n to (i+1)*n-1 of the 
                   original array.
    
    Mathematical property: Concatenating all sub-vectors in order reconstructs
                          the original vector.
-/
theorem dsplit_spec {n k : Nat} (arr : Vector Float (k * n))
  (h : k > 0) :
  ⦃⌜k > 0⌝⦄
  dsplit arr k ⟨rfl, h⟩
  ⦃⇓result => ⌜result.length = k ∧
              ∀ i : Fin k, ∃ sub ∈ result,
                ∀ j : Fin n, sub.get j = arr.get ⟨i.val * n + j.val, by
                  have h1 : i.val < k := i.isLt
                  have h2 : j.val < n := j.isLt
                  calc i.val * n + j.val
                    < i.val * n + n := Nat.add_lt_add_left h2 _
                    _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
                    _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
                ⟩⌝⦄ := by
  triple_intro h_pre
  simp [dsplit]
  constructor
  · exact list_length_range_map _ k
  · intro i
    exact range_map_membership arr i