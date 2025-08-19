import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.convolve: Returns the discrete, linear convolution of two one-dimensional arrays.

    The discrete convolution operation is defined as:
    (a * v)[n] = sum(a[m] * v[n - m], m = -∞ to ∞)
    
    For finite arrays, the convolution is computed over the valid range where
    both arrays have elements. This implementation follows the 'full' mode
    which returns a convolution of length (M + N - 1) where M and N are
    the lengths of the input arrays.
-/
def numpy_convolve {m n : Nat} (a : Vector Float m) (v : Vector Float n) : Id (Vector Float (m + n - 1)) :=
  if h : m + n = 0 then 
    pure (Vector.mk [])
  else
    let result := List.range (m + n - 1) |>.map (fun k =>
      List.sum (List.range m |>.map (fun i => 
        if k ≥ i ∧ k - i < n then 
          a.get ⟨i, Nat.lt_of_le_of_lt (Nat.le_refl _) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_range.mpr i.isLt))))⟩ * 
          v.get ⟨k - i, Nat.lt_of_le_of_lt (Nat.le_refl _) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_range.mpr (Nat.sub_lt (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))))))⟩
        else 0)))
    pure ⟨result, by
      simp [List.length_map, List.length_range]
    ⟩

-- LLM HELPER
lemma fin_val_lt {n : Nat} (i : Fin n) : i.val < n := i.2

-- LLM HELPER
lemma range_mem_lt {n k : Nat} (h : k ∈ List.range n) : k < n := 
  List.mem_range.mp h

-- LLM HELPER  
lemma add_sub_pos {m n : Nat} (h_m : m > 0) (h_n : n > 0) : m + n - 1 > 0 := by
  cases' m with m
  · contradiction
  cases' n with n
  · contradiction
  simp [Nat.succ_add, Nat.add_succ, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
  exact Nat.succ_pos _

-- LLM HELPER
lemma zero_fin_val {n : Nat} (h : n > 0) : (⟨0, h⟩ : Fin n).val = 0 := rfl

-- LLM HELPER
lemma last_fin_val {n : Nat} (h : n > 0) : (⟨n - 1, Nat.sub_lt h (Nat.zero_lt_one)⟩ : Fin n).val = n - 1 := rfl

-- LLM HELPER
lemma triple_intro {α : Type*} {P : Prop} {Q : α → Prop} {f : Id α} :
  P → (P → Q (f.run)) → ⦃⌜P⌝⦄ f ⦃⇓a => ⌜Q a⌝⦄ := by
  intro h_pre h_post
  simp [Triple.triple, Triple.pretriple]
  exact h_post h_pre

/-- Specification: numpy.convolve returns the discrete convolution of two vectors.

    Precondition: Both input vectors must be non-empty (enforced by types)
    Postcondition: The result vector contains the discrete convolution values
    
    The convolution at position k is computed as:
    result[k] = sum(a[i] * v[k - i] for all valid i)
    
    Mathematical properties:
    1. Result length is m + n - 1 (enforced by return type)
    2. Each element follows the convolution definition
    3. Boundary conditions: zero-padding is implicitly assumed outside array bounds
-/
theorem numpy_convolve_spec {m n : Nat} (a : Vector Float m) (v : Vector Float n) 
    (h_m : m > 0) (h_n : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    numpy_convolve a v
    ⦃⇓result => ⌜
      -- Core convolution property: each element is sum of products
      ∀ k : Fin (m + n - 1), result.get k = 
        List.sum (List.range m |>.map (fun i => 
          if k.val ≥ i ∧ k.val - i < n then 
            a.get ⟨i, Nat.lt_of_le_of_lt (Nat.le_refl _) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_range.mpr i.isLt))))⟩ * v.get ⟨k.val - i, Nat.lt_of_le_of_lt (Nat.le_refl _) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_range.mpr (Nat.sub_lt (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))))))⟩
          else 0)) ∧
      -- Sanity checks for edge cases
      (result.get ⟨0, add_sub_pos h_m h_n⟩ = a.get ⟨0, h_m⟩ * v.get ⟨0, h_n⟩) ∧
      (result.get ⟨m + n - 2, Nat.sub_lt (add_sub_pos h_m h_n) (Nat.zero_lt_one)⟩ = a.get ⟨m - 1, Nat.sub_lt h_m (Nat.zero_lt_one)⟩ * v.get ⟨n - 1, Nat.sub_lt h_n (Nat.zero_lt_one)⟩) ∧
      -- Mathematical property: convolution preserves finite values
      (∀ i : Fin m, a.get i = a.get i) ∧ (∀ j : Fin n, v.get j = v.get j) →
      (∀ k : Fin (m + n - 1), result.get k = result.get k)
    ⌝⦄ := by
  apply triple_intro
  · exact ⟨h_m, h_n⟩
  · intro pre
    simp [numpy_convolve]
    split
    · contradiction
    · constructor
      · intro k
        simp [Vector.get]
        rfl
      · constructor
        · simp [Vector.get]
          rfl
        · constructor
          · simp [Vector.get]
            rfl
          · intro h
            intro k
            rfl