import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def make_subarray {n k : Nat} (arr : Vector Float n) (part_idx : Fin k) 
    (h_divides : k > 0 ∧ n % k = 0) : Vector Float (n / k) :=
  let chunk_size := n / k
  Vector.mk (List.range chunk_size).map (fun elem_idx => 
    arr.get ⟨part_idx.val * chunk_size + elem_idx, by
      have h1 : part_idx.val < k := part_idx.isLt
      have h2 : elem_idx < chunk_size := List.mem_range.mp (List.get_mem _ _)
      have h3 : chunk_size * k = n := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_divides.2)
      calc part_idx.val * chunk_size + elem_idx
        < part_idx.val * chunk_size + chunk_size := Nat.add_lt_add_left h2 _
        _ = (part_idx.val + 1) * chunk_size := by ring
        _ ≤ k * chunk_size := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
        _ = chunk_size * k := Nat.mul_comm _ _
        _ = n := h3⟩)

/-- Split a 1D array into multiple sub-arrays horizontally.
    For simplicity, we focus on the 1D case where the array is split into 
    k equal parts. In numpy, hsplit on 1D arrays is equivalent to split with axis=0. -/
def hsplit {n k : Nat} (arr : Vector Float n) 
    (h_divides : k > 0 ∧ n % k = 0) : 
    Id (Vector (Vector Float (n / k)) k) :=
  Vector.mk (List.range k).map (fun i => 
    make_subarray arr ⟨i, List.mem_range.mp (List.get_mem _ _)⟩ h_divides)

-- LLM HELPER
lemma index_bound {n k : Nat} (part_idx : Fin k) (elem_idx : Fin (n / k)) 
    (h_divides : k > 0 ∧ n % k = 0) : 
    part_idx.val * (n / k) + elem_idx.val < n := by
  have h1 : part_idx.val < k := part_idx.isLt
  have h2 : elem_idx.val < n / k := elem_idx.isLt
  have h3 : (n / k) * k = n := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_divides.2)
  calc part_idx.val * (n / k) + elem_idx.val
    < part_idx.val * (n / k) + (n / k) := Nat.add_lt_add_left h2 _
    _ = (part_idx.val + 1) * (n / k) := by ring
    _ ≤ k * (n / k) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    _ = (n / k) * k := Nat.mul_comm _ _
    _ = n := h3

-- LLM HELPER
lemma unique_decomposition {n k : Nat} (i : Fin n) (h_divides : k > 0 ∧ n % k = 0) :
    ∃ (p : Fin k) (e : Fin (n / k)), i.val = p.val * (n / k) + e.val := by
  let chunk_size := n / k
  let p_val := i.val / chunk_size
  let e_val := i.val % chunk_size
  have h_chunk_pos : chunk_size > 0 := by
    by_cases h : n = 0
    · simp [h, chunk_size]
      omega
    · exact Nat.div_pos (Nat.pos_of_ne_zero h) h_divides.1
  have h1 : p_val < k := by
    have : p_val * chunk_size ≤ i.val := Nat.div_mul_le_self _ _
    have : i.val < n := i.isLt
    have : p_val * chunk_size < n := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) this
    rw [← Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_divides.2)] at this
    exact Nat.div_lt_iff_lt_mul h_chunk_pos.ne' |>.mpr this
  have h2 : e_val < chunk_size := Nat.mod_lt _ h_chunk_pos
  use ⟨p_val, h1⟩, ⟨e_val, h2⟩
  exact Nat.div_add_mod _ _

/-- Specification: hsplit divides a 1D array into k equal sub-arrays.
    Each sub-array has n/k elements. The i-th sub-array contains elements 
    from index i*(n/k) to (i+1)*(n/k)-1 of the original array.
    
    Mathematical properties:
    1. The concatenation of all sub-arrays equals the original array
    2. Each sub-array has exactly n/k elements
    3. Elements are distributed in order without overlapping -/
theorem hsplit_spec {n k : Nat} (arr : Vector Float n) 
    (h_divides : k > 0 ∧ n % k = 0) :
    ⦃⌜k > 0 ∧ n % k = 0⌝⦄
    hsplit arr h_divides
    ⦃⇓result => ⌜(∀ (part_idx : Fin k) (elem_idx : Fin (n / k)),
                  (result.get part_idx).get elem_idx = 
                  arr.get ⟨part_idx.val * (n / k) + elem_idx.val, index_bound part_idx elem_idx h_divides⟩) ∧
                 (∀ i : Fin n, ∃ (p : Fin k) (e : Fin (n / k)), 
                  i.val = p.val * (n / k) + e.val ∧
                  arr.get i = (result.get p).get e)⌝⦄ := by
  simp [triple_spec]
  intro h
  constructor
  · intro part_idx elem_idx
    simp [hsplit, make_subarray]
    congr
  · intro i
    obtain ⟨p, e, h_eq⟩ := unique_decomposition i h_divides
    use p, e
    constructor
    · exact h_eq
    · simp [hsplit, make_subarray]
      congr
      exact h_eq