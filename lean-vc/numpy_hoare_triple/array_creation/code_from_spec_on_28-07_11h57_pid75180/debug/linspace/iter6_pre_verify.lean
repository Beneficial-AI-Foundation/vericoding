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
    -- LLM HELPER
    have h_length : #[start].size = num := by simp; omega
    pure ⟨#[start], h_length⟩
  else
    let step := (stop - start) / (num - 1).toFloat
    let values := Array.range num |>.map (fun i => start + i.toFloat * step)
    -- LLM HELPER  
    have h_length : values.size = num := by
      simp [values, Array.size_map, Array.size_range]
    pure ⟨values, h_length⟩

-- LLM HELPER
lemma Array.get_range_map {n : Nat} {f : Nat → α} (i : Fin n) :
  (Array.range n |>.map f)[i.val]'(by simp [Array.size_map, Array.size_range]; exact i.isLt) = f i.val := by
  simp [Array.getElem_map, Array.getElem_range]

-- LLM HELPER
lemma Nat.sub_pos_of_lt {n : Nat} (h : n > 1) : n - 1 > 0 := by
  omega

-- LLM HELPER
lemma Nat.sub_ne_zero_of_lt {n : Nat} (h : n > 1) : n - 1 ≠ 0 := by
  omega

-- LLM HELPER  
lemma Float.div_pos {a b : Float} (ha : a > 0) (hb : b > 0) : a / b > 0 := by
  exact Float.div_pos ha hb

-- LLM HELPER
lemma Float.div_neg_of_neg_of_pos {a b : Float} (ha : a < 0) (hb : b > 0) : a / b < 0 := by
  exact Float.div_neg_of_neg_of_pos ha hb

-- LLM HELPER
lemma Float.div_nonneg {a b : Float} (ha : a ≥ 0) (hb : b ≥ 0) : a / b ≥ 0 := by
  exact Float.div_nonneg ha hb

-- LLM HELPER
lemma Float.div_nonpos_of_nonpos_of_nonneg {a b : Float} (ha : a ≤ 0) (hb : b ≥ 0) : a / b ≤ 0 := by
  exact Float.div_nonpos_of_nonpos_of_nonneg ha hb

-- LLM HELPER
lemma Fin.val_lt_of_lt {n : Nat} {i j : Fin n} (h : i < j) : i.val < j.val := by
  exact h

-- LLM HELPER
lemma Float.div_mul_cancel {a b : Float} (hb : b ≠ 0) : (a / b) * b = a := by
  exact Float.div_mul_cancel a hb

-- LLM HELPER
lemma ne_of_gt {α : Type*} [LinearOrder α] {a b : α} (h : a > b) : a ≠ b := by
  exact Ne.symm (ne_of_lt h)

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
def problem_spec {num : Nat} (linspace_fn : (start stop : Float) → (h : num > 0) → Id (Vector Float num)) (start stop : Float) (h : num > 0) :=
    ⦃⌜num > 0⌝⦄
    linspace_fn start stop h
    ⦃⇓result => ⌜
      -- First element is always start
      result.get ⟨0, h⟩ = start ∧
      
      -- Special case: when num = 1, the single element is start
      (num = 1 → ∀ i : Fin num, result.get i = start) ∧
      
      -- General case: when num > 1
      (1 < num → 
        let step := (stop - start) / (num - 1).toFloat
        -- Last element is stop
        (result.get ⟨num - 1, Nat.pred_lt (Ne.symm (ne_of_gt h))⟩ = stop) ∧
        -- All elements follow the linear formula
        (∀ i : Fin num, result.get i = start + i.val.toFloat * step) ∧
        -- Consecutive elements have constant spacing
        (∀ i j : Fin num, i.val + 1 = j.val → 
          result.get j - result.get i = step)) ∧
      
      -- Monotonicity property
      ((start < stop) → ∀ i j : Fin num, i < j → result.get i < result.get j) ∧
      ((stop < start) → ∀ i j : Fin num, i < j → result.get j < result.get i) ∧
      ((start = stop) → ∀ i : Fin num, result.get i = start) ∧
      
      -- Bounds property: all elements lie within the interval
      (∀ i : Fin num, 
        result.get i ≥ min start stop ∧ 
        result.get i ≤ max start stop) ∧
      
      -- Linear interpolation property: each element is a weighted average
      (1 < num → ∀ i : Fin num,
        let t := i.val.toFloat / (num - 1).toFloat
        result.get i = (1 - t) * start + t * stop) ∧
      
      -- Reverse symmetry property
      (1 < num → ∀ i : Fin num,
        i.val < num - 1 → 
        let j_val := num - 1 - i.val
        j_val < num → 
        result.get i = stop - (i.val.toFloat * (stop - start) / (num - 1).toFloat))
    ⌝⦄

theorem correctness {num : Nat} (start stop : Float) (h : num > 0) :
    problem_spec linspace start stop h := by
  simp [problem_spec, linspace, hoare_pure_spec]
  split_ifs with h_eq
  · -- Case: num = 1
    simp [h_eq]
    constructor
    · -- First element is start
      simp [Vector.get]
      rfl
    constructor
    · -- When num = 1, all elements equal start
      intro _ i
      simp [h_eq] at i
      interval_cases i.val
      simp [Vector.get]
      rfl
    constructor
    · -- When num > 1 (contradiction)
      intro h_gt1
      rw [h_eq] at h_gt1
      norm_num at h_gt1
    constructor
    · -- Monotonicity (increasing)
      intro _ i j h_lt
      simp [h_eq] at i j h_lt
      interval_cases i.val j.val
      norm_num at h_lt
    constructor
    · -- Monotonicity (decreasing)
      intro _ i j h_lt
      simp [h_eq] at i j h_lt
      interval_cases i.val j.val
      norm_num at h_lt
    constructor
    · -- When start = stop
      intro _ i
      simp [h_eq] at i
      interval_cases i.val
      simp [Vector.get]
      rfl
    constructor
    · -- Bounds property
      intro i
      simp [h_eq] at i
      interval_cases i.val
      simp [Vector.get, min_def, max_def]
      split_ifs <;> simp
    constructor
    · -- Linear interpolation (num > 1 contradiction)
      intro h_gt1
      rw [h_eq] at h_gt1
      norm_num at h_gt1
    · -- Reverse symmetry (num > 1 contradiction)
      intro h_gt1
      rw [h_eq] at h_gt1
      norm_num at h_gt1
  · -- Case: num > 1
    have h_gt1 : 1 < num := by
      cases' Nat.eq_or_lt_of_le (Nat.pos_iff_ne_zero.mp h) with h_eq' h_lt
      · exact absurd h_eq' h_eq
      · exact h_lt
    simp
    let step := (stop - start) / (num - 1).toFloat
    let values := Array.range num |>.map (fun i => start + i.toFloat * step)
    constructor
    · -- First element is start
      simp [Vector.get, Array.get_range_map]
      ring
    constructor
    · -- When num = 1 (contradiction)
      intro h_eq'
      exact absurd h_eq' h_eq
    constructor
    · -- When num > 1
      intro _
      constructor
      · -- Last element is stop
        simp [Vector.get, Array.get_range_map]
        simp [step]
        ring_nf
        congr 1 
        simp only [Float.div_mul_cancel]
        norm_cast
        exact Nat.sub_ne_zero_of_lt h_gt1
      constructor
      · -- Linear formula
        intro i
        simp [Vector.get, Array.get_range_map]
      · -- Constant spacing
        intro i j h_succ
        simp [Vector.get, Array.get_range_map]
        simp [step]
        ring_nf
        congr 2
        rw [h_succ]
        simp
        ring
    constructor
    · -- Monotonicity (increasing)
      intro h_start_lt i j h_ij
      simp [Vector.get, Array.get_range_map]
      simp [step]
      have h_step_pos : (stop - start) / (num - 1).toFloat > 0 := by
        apply Float.div_pos h_start_lt
        norm_cast
        exact Nat.sub_pos_of_lt h_gt1
      have h_coeff : i.val.toFloat < j.val.toFloat := by
        norm_cast
        exact Fin.val_lt_of_lt h_ij
      linarith
    constructor
    · -- Monotonicity (decreasing)
      intro h_start_gt i j h_ij
      simp [Vector.get, Array.get_range_map]
      simp [step]
      have h_step_neg : (stop - start) / (num - 1).toFloat < 0 := by
        apply Float.div_neg_of_neg_of_pos h_start_gt
        norm_cast
        exact Nat.sub_pos_of_lt h_gt1
      have h_coeff : i.val.toFloat < j.val.toFloat := by
        norm_cast
        exact Fin.val_lt_of_lt h_ij
      linarith
    constructor
    · -- When start = stop
      intro h_eq_start_stop i
      simp [Vector.get, Array.get_range_map]
      simp [step, h_eq_start_stop]
      ring
    constructor
    · -- Bounds property
      intro i
      simp [Vector.get, Array.get_range_map]
      simp [step]
      constructor
      · -- Lower bound
        by_cases h_le : start ≤ stop
        · simp [min_def, h_le]
          have h_nonneg : 0 ≤ i.val.toFloat := by norm_cast; exact Nat.zero_le _
          have h_step_nonneg : 0 ≤ (stop - start) / (num - 1).toFloat := by
            apply Float.div_nonneg (le_of_lt h_le)
            norm_cast
            exact Nat.zero_le _
          linarith
        · simp [min_def, h_le]
          push_neg at h_le
          have h_le_bound : i.val.toFloat ≤ (num - 1).toFloat := by
            norm_cast
            omega
          have h_step_neg : (stop - start) / (num - 1).toFloat ≤ 0 := by
            apply Float.div_nonpos_of_nonpos_of_nonneg (le_of_lt h_le)
            norm_cast
            exact Nat.zero_le _
          linarith
      · -- Upper bound
        by_cases h_le : start ≤ stop
        · simp [max_def, h_le]
          have h_le_bound : i.val.toFloat ≤ (num - 1).toFloat := by
            norm_cast
            omega
          have h_step_nonneg : 0 ≤ (stop - start) / (num - 1).toFloat := by
            apply Float.div_nonneg (le_of_lt h_le)
            norm_cast
            exact Nat.zero_le _
          linarith
        · simp [max_def, h_le]
          push_neg at h_le
          have h_nonneg : 0 ≤ i.val.toFloat := by norm_cast; exact Nat.zero_le _
          have h_step_neg : (stop - start) / (num - 1).toFloat ≤ 0 := by
            apply Float.div_nonpos_of_nonpos_of_nonneg (le_of_lt h_le)
            norm_cast
            exact Nat.zero_le _
          linarith
    constructor
    · -- Linear interpolation
      intro _ i
      simp [Vector.get, Array.get_range_map]
      simp [step]
      ring_nf
      congr 1
      ring
    · -- Reverse symmetry  
      intro _ i _ _ _
      simp [Vector.get, Array.get_range_map]
      simp [step]
      ring