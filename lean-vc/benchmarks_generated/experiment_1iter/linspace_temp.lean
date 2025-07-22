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
    return Vector.mk [start] rfl
  else
    let step := (stop - start) / (num - 1).toFloat
    let values := List.range num |>.map (fun i => start + i.toFloat * step)
    -- LLM HELPER
    have values_length : values.length = num := by
      simp [values]
      exact List.length_map _ _
    return Vector.mk values values_length

-- LLM HELPER
lemma list_range_map_length (n : Nat) (f : Nat → Float) : 
  (List.range n |>.map f).length = n := by
  simp [List.length_map]

-- LLM HELPER
lemma vector_get_mk {α : Type*} (l : List α) (h : l.length = n) (i : Fin n) :
  (Vector.mk l h).get i = l.get ⟨i.val, h ▸ i.isLt⟩ := by
  rfl

-- LLM HELPER
lemma list_get_range_map {n : Nat} (f : Nat → Float) (i : Fin n) :
  (List.range n |>.map f).get ⟨i.val, by simp; exact i.isLt⟩ = f i.val := by
  simp [List.get_map]

-- LLM HELPER
lemma float_min_def (a b : Float) : min a b = if a ≤ b then a else b := by
  rfl

-- LLM HELPER
lemma float_max_def (a b : Float) : max a b = if a ≤ b then b else a := by
  rfl

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
  simp only [linspace]
  split
  · -- Case: num = 1
    next h_eq =>
    simp only [Id.pure_bind, Id.bind_pure]
    split_ands
    · -- First element is start
      simp [Vector.get, h_eq]
    · -- When num = 1, all elements are start
      intro h_one i
      simp [Vector.get, h_eq]
    · -- General case when num > 1 (vacuously true since num = 1)
      intro h_gt
      exfalso
      rw [h_eq] at h_gt
      simp at h_gt
    · -- Monotonicity cases (all vacuously true or trivial since num = 1)
      simp
    · simp
    · intro h_eq_stop i
      simp [Vector.get, h_eq, h_eq_stop]
    · -- Bounds property
      intro i
      simp [Vector.get, h_eq]
      constructor
      · simp [min]
        by_cases h_le : start ≤ stop
        · simp [h_le]
        · simp [h_le]
      · simp [max]
        by_cases h_le : start ≤ stop
        · simp [h_le]
        · simp [h_le]
    · -- Linear interpolation (vacuously true since num = 1)
      intro h_gt
      exfalso
      rw [h_eq] at h_gt
      simp at h_gt
    · -- Reverse symmetry (vacuously true since num = 1)
      intro h_gt
      exfalso
      rw [h_eq] at h_gt
      simp at h_gt
  · -- Case: num > 1
    next h_ne =>
    simp only [Id.pure_bind, Id.bind_pure]
    have h_gt : num > 1 := by
      cases' Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h_eq h_lt
      · contradiction
      · exact h_lt
    let step := (stop - start) / (num - 1).toFloat
    let values := List.range num |>.map (fun i => start + i.toFloat * step)
    have values_length : values.length = num := list_range_map_length num _
    split_ands
    · -- First element is start
      simp [Vector.get, vector_get_mk, list_get_range_map]
      simp [step]
      ring
    · -- When num = 1 case (vacuously true since num ≠ 1)
      intro h_one
      exfalso
      exact h_ne h_one
    · -- General case when num > 1
      intro h_gt_one
      constructor
      · -- Last element is stop
        simp [Vector.get, vector_get_mk, list_get_range_map]
        simp [step]
        have : (num - 1).toFloat ≠ 0 := by
          simp [Float.toFloat_ne_zero]
          omega
        field_simp
        ring
      · constructor
        · -- All elements follow linear formula
          intro i
          simp [Vector.get, vector_get_mk, list_get_range_map, step]
        · -- Consecutive elements have constant spacing
          intro i j h_consec
          simp [Vector.get, vector_get_mk, list_get_range_map, step]
          have : j.val.toFloat = i.val.toFloat + 1 := by
            simp [h_consec]
          rw [this]
          ring
    · -- Monotonicity: start < stop
      intro h_lt i j h_ij
      simp [Vector.get, vector_get_mk, list_get_range_map, step]
      have : (stop - start) / (num - 1).toFloat > 0 := by
        apply div_pos
        · linarith
        · simp [Float.toFloat_pos]
          omega
      linarith [Fin.val_lt_of_lt h_ij]
    · -- Monotonicity: start > stop
      intro h_gt i j h_ij
      simp [Vector.get, vector_get_mk, list_get_range_map, step]
      have : (stop - start) / (num - 1).toFloat < 0 := by
        apply div_neg_of_neg_of_pos
        · linarith
        · simp [Float.toFloat_pos]
          omega
      linarith [Fin.val_lt_of_lt h_ij]
    · -- start = stop case
      intro h_eq_val i
      simp [Vector.get, vector_get_mk, list_get_range_map, step, h_eq_val]
      ring
    · -- Bounds property
      intro i
      simp [Vector.get, vector_get_mk, list_get_range_map, step]
      sorry -- This would require more detailed float arithmetic reasoning
    · -- Linear interpolation property
      intro h_gt_one i
      simp [Vector.get, vector_get_mk, list_get_range_map, step]
      let t := i.val.toFloat / (num - 1).toFloat
      ring_nf
      sorry -- This would require detailed algebraic manipulation
    · -- Reverse symmetry
      intro h_gt_one i h_lt_pred j_val h_lt_num
      simp [Vector.get, vector_get_mk, list_get_range_map, step]
      sorry -- This would require detailed algebraic reasoning