import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.linspace: Return evenly spaced numbers over a specified interval.
    
    Returns num evenly spaced samples, calculated over the interval [start, stop]
    when endpoint is true (default), or [start, stop) when endpoint is false.
    
    This specification focuses on the most common use case where endpoint=true,
    returning num samples that are evenly distributed from start to stop inclusive.
-/
def linspace {num : Nat} (start stop : Float) (h : num > 0) : Id (Vector Float num) :=
  if num = 1 then
    return Vector.replicate num start
  else
    let step := (stop - start) / (num - 1).toFloat
    let values := Array.range num |>.map (fun i => start + i.toFloat * step)
    return ⟨values, by simp [Array.size_map, Array.size_range]⟩

-- LLM HELPER
lemma vector_get_replicate {n : Nat} (a : Float) (i : Fin n) (hn : n > 0) :
  (Vector.replicate n a).get i = a := by
  simp [Vector.replicate, Vector.get]

-- LLM HELPER  
lemma array_get_map_range (f : Nat → Float) (n : Nat) (i : Fin n) :
  (Array.range n |>.map f).get ⟨i.val, by simp [Array.size_map, Array.size_range]; exact i.isLt⟩ = f i.val := by
  simp [Array.get_map, Array.get_range]

-- LLM HELPER
lemma nat_sub_lt_of_pos {n : Nat} (h : n > 0) : n - 1 < n := by
  cases n with
  | zero => contradiction
  | succ k => simp [Nat.succ_sub_succ_eq_sub, Nat.zero_sub, Nat.lt_succ_self]

-- LLM HELPER
lemma fin_val_sub {n : Nat} (i : Fin n) (h : n > 1) : 
  (⟨n - 1, nat_sub_lt_of_pos (by omega)⟩ : Fin n).val = n - 1 := by
  simp

-- LLM HELPER
lemma float_div_cancel {a b : Float} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_mul_cancel]
  exact hb

-- LLM HELPER
lemma toFloat_sub_one {n : Nat} (h : n > 1) : (n - 1).toFloat ≠ 0 := by
  simp [Float.coe_nat_ne_zero_iff]
  omega

/-- Specification: numpy.linspace returns a vector of evenly spaced values.
    
    When num > 0 and endpoint=true (default behavior):
    - The first element equals start
    - The last element equals stop (when num > 1)
    - Elements are evenly spaced with step = (stop - start) / (num - 1) when num > 1
    - When num = 1, the single element equals start
    
    Mathematical properties:
    - For any valid index i, the element value is: start + i * step
    - The spacing between consecutive elements is constant (except when num = 1)
    - The sequence is monotonic (increasing if start < stop, decreasing if start > stop)
    - All elements lie within [min(start, stop), max(start, stop)]
    - Linear interpolation property: each element represents a linear interpolation between start and stop
    
    Sanity checks:
    - Size of result vector equals num
    - When start = stop, all elements equal start
    - The function is symmetric: reversing start and stop reverses the sequence
    - Consecutive differences are constant for num > 2
-/
theorem linspace_spec {num : Nat} (start stop : Float) (h : num > 0) :
    ⦃⌜num > 0⌝⦄
    linspace start stop h
    ⦃⇓result => ⌜
      -- First element is always start
      result.get ⟨0, h⟩ = start ∧
      
      -- Special case: when num = 1, the single element is start
      (num = 1 → ∀ i : Fin num, result.get i = start) ∧
      
      -- General case: when num > 1
      (num > 1 → 
        let step := (stop - start) / (num - 1).toFloat
        -- Last element is stop
        (result.get ⟨num - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = stop) ∧
        -- All elements follow the linear formula
        (∀ i : Fin num, result.get i = start + i.val.toFloat * step) ∧
        -- Consecutive elements have constant spacing
        (∀ i j : Fin num, i.val + 1 = j.val → 
          result.get j - result.get i = step)) ∧
      
      -- Monotonicity property
      ((start < stop) → ∀ i j : Fin num, i < j → result.get i < result.get j) ∧
      ((start > stop) → ∀ i j : Fin num, i < j → result.get i > result.get j) ∧
      ((start = stop) → ∀ i : Fin num, result.get i = start) ∧
      
      -- Bounds property: all elements lie within the interval
      (∀ i : Fin num, 
        result.get i ≥ min start stop ∧ 
        result.get i ≤ max start stop) ∧
      
      -- Linear interpolation property: each element can be expressed as a weighted average
      (num > 1 → ∀ i : Fin num,
        let t := i.val.toFloat / (num - 1).toFloat
        result.get i = (1 - t) * start + t * stop) ∧
      
      -- Reverse symmetry: if we compute linspace(stop, start, num), 
      -- element i equals element (num-1-i) of linspace(start, stop, num)
      (num > 1 → ∀ i : Fin num,
        i.val < num - 1 → 
        let j_val := num - 1 - i.val
        j_val < num → 
        result.get i = stop - (i.val.toFloat * (stop - start) / (num - 1).toFloat))
    ⌝⦄ := by
  rw [triple_spec]
  simp [linspace]
  constructor
  · exact h
  · intro _
    split_ifs with h_eq
    · -- Case: num = 1
      simp [h_eq]
      constructor
      · simp [vector_get_replicate]
      constructor
      · intro _ i
        simp [vector_get_replicate]
      constructor
      · intro h_gt
        omega
      constructor
      · intro _ i j h_lt
        simp [vector_get_replicate]
      constructor
      · intro _ i j h_lt
        simp [vector_get_replicate] 
      constructor
      · intro _ i
        simp [vector_get_replicate]
      constructor
      · intro i
        simp [vector_get_replicate, min_def, max_def]
        split_ifs <;> simp
      constructor
      · intro h_gt
        omega
      · intro h_gt i h_i_lt _ _
        omega
    · -- Case: num > 1
      have h_gt : num > 1 := by
        cases' Nat.eq_or_lt_of_le (Nat.one_le_of_lt h) with h_eq' h_lt
        · contradiction
        · exact h_lt
      simp [h_gt]
      let step := (stop - start) / (num - 1).toFloat
      let values := Array.range num |>.map (fun i => start + i.toFloat * step)
      have h_size : values.size = num := by simp [Array.size_map, Array.size_range]
      
      constructor
      · -- First element is start
        simp [Vector.get, h_size]
        rw [array_get_map_range]
        simp [step]
      
      constructor
      · -- num = 1 case (contradiction)
        intro h_eq'
        omega
      
      constructor
      · -- num > 1 case
        intro _
        constructor
        · -- Last element is stop
          simp [Vector.get, h_size]
          rw [array_get_map_range]
          simp [step]
          rw [add_comm start, ← sub_eq_iff_eq_add]
          rw [mul_div_cancel]
          · ring
          · exact toFloat_sub_one h_gt
        
        constructor
        · -- Linear formula
          intro i
          simp [Vector.get, h_size]
          rw [array_get_map_range]
          
        · -- Constant spacing
          intro i j h_ij
          simp [Vector.get, h_size]
          rw [array_get_map_range, array_get_map_range]
          simp [step]
          have : j.val.toFloat = i.val.toFloat + 1 := by
            simp [← h_ij, Nat.cast_add, Nat.cast_one]
          rw [this]
          ring
      
      constructor
      · -- Monotonicity (increasing)
        intro h_inc i j h_ij
        simp [Vector.get, h_size]
        rw [array_get_map_range, array_get_map_range]
        simp [step]
        have h_pos : (stop - start) / (num - 1).toFloat > 0 := by
          rw [div_pos_iff]
          left
          constructor
          · linarith
          · simp [Float.coe_nat_pos_iff]
            omega
        have : i.val.toFloat < j.val.toFloat := by
          simp [Fin.lt_iff_val_lt_val] at h_ij
          exact Nat.cast_lt.mpr h_ij
        linarith [mul_lt_mul_of_pos_right this h_pos]
      
      constructor
      · -- Monotonicity (decreasing)
        intro h_dec i j h_ij
        simp [Vector.get, h_size]
        rw [array_get_map_range, array_get_map_range]
        simp [step]
        have h_neg : (stop - start) / (num - 1).toFloat < 0 := by
          rw [div_neg_iff]
          left
          constructor
          · linarith
          · simp [Float.coe_nat_pos_iff]
            omega
        have : i.val.toFloat < j.val.toFloat := by
          simp [Fin.lt_iff_val_lt_val] at h_ij
          exact Nat.cast_lt.mpr h_ij
        linarith [mul_lt_mul_of_neg_right this h_neg]
      
      constructor
      · -- Equal case
        intro h_eq i
        simp [Vector.get, h_size]
        rw [array_get_map_range]
        simp [step, h_eq]
        ring
      
      constructor
      · -- Bounds property
        intro i
        simp [Vector.get, h_size]
        rw [array_get_map_range]
        simp [step]
        constructor
        · simp [min_def]
          split_ifs with h_le
          · -- start ≤ stop
            have h_nonneg : (stop - start) / (num - 1).toFloat ≥ 0 := by
              rw [div_nonneg_iff]
              left
              constructor
              · linarith
              · simp [Float.coe_nat_nonneg]
            have : i.val.toFloat * ((stop - start) / (num - 1).toFloat) ≥ 0 := by
              apply mul_nonneg
              · simp [Float.coe_nat_nonneg]
              · exact h_nonneg
            linarith
          · -- start > stop
            have h_nonpos : (stop - start) / (num - 1).toFloat ≤ 0 := by
              rw [div_nonpos_iff]
              left
              constructor
              · linarith
              · simp [Float.coe_nat_pos_iff]
                omega
            have h_bound : i.val.toFloat ≤ (num - 1).toFloat := by
              simp [Nat.cast_le]
              exact Nat.le_sub_one_of_lt i.isLt
            have : i.val.toFloat * ((stop - start) / (num - 1).toFloat) ≥ (stop - start) := by
              cases' le_or_lt i.val (num - 1) with h_le' h_gt'
              · rw [← mul_one (stop - start)]
                rw [← div_mul_cancel (stop - start) (toFloat_sub_one h_gt)]
                apply mul_le_mul_of_nonpos_right
                · exact h_bound
                · exact h_nonpos
              · have : i.val = num - 1 := by omega
                simp [this]
                rw [mul_div_cancel]
                exact toFloat_sub_one h_gt
            linarith
            
        · simp [max_def]
          split_ifs with h_le
          · -- start ≤ stop
            have h_nonneg : (stop - start) / (num - 1).toFloat ≥ 0 := by
              rw [div_nonneg_iff]
              left
              constructor
              · linarith
              · simp [Float.coe_nat_nonneg]
            have h_bound : i.val.toFloat ≤ (num - 1).toFloat := by
              simp [Nat.cast_le]
              exact Nat.le_sub_one_of_lt i.isLt
            have : i.val.toFloat * ((stop - start) / (num - 1).toFloat) ≤ (stop - start) := by
              rw [← mul_one (stop - start)]
              rw [← div_mul_cancel (stop - start) (toFloat_sub_one h_gt)]
              apply mul_le_mul_of_nonneg_right h_bound h_nonneg
            linarith
          · -- start > stop
            have h_nonpos : (stop - start) / (num - 1).toFloat ≤ 0 := by
              rw [div_nonpos_iff]
              left
              constructor
              · linarith
              · simp [Float.coe_nat_pos_iff]
                omega
            have : i.val.toFloat * ((stop - start) / (num - 1).toFloat) ≤ 0 := by
              apply mul_nonpos_of_nonneg_of_nonpos
              · simp [Float.coe_nat_nonneg]
              · exact h_nonpos
            linarith
      
      constructor
      · -- Linear interpolation
        intro _ i
        simp [Vector.get, h_size]
        rw [array_get_map_range]
        let t := i.val.toFloat / (num - 1).toFloat
        simp [t]
        ring_nf
        rw [← add_div, mul_div_assoc, mul_div_cancel]
        · ring
        · exact toFloat_sub_one h_gt
      
      · -- Reverse symmetry  
        intro _ i h_i_lt h_j_bound
        simp [Vector.get, h_size]
        rw [array_get_map_range]
        simp [step]
        ring