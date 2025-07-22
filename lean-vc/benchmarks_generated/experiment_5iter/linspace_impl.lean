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
  pure (Vector.ofFn fun i => 
    if num = 1 then start 
    else start + i.val.toFloat * (stop - start) / (num - 1).toFloat)

-- LLM HELPER
lemma vector_get_ofFn {n : Nat} (f : Fin n → Float) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  rfl

-- LLM HELPER
lemma toFloat_zero : (0 : Nat).toFloat = 0 := by
  rfl

-- LLM HELPER
lemma toFloat_sub_one (n : Nat) (h : n > 0) : 
  (n - 1).toFloat = n.toFloat - 1 := by
  cases n with
  | zero => contradiction
  | succ n => simp [Nat.succ_sub_succ]

-- LLM HELPER
lemma div_self_ne_zero (x : Float) (h : x ≠ 0) : x / x = 1 := by
  exact Float.div_self h

-- LLM HELPER
lemma zero_div (x : Float) : 0 / x = 0 := by
  exact Float.zero_div x

-- LLM HELPER
lemma fin_val_lt_of_lt {n : Nat} (i j : Fin n) (h : i < j) : i.val < j.val := by
  exact h

-- LLM HELPER
lemma fin_val_zero {n : Nat} (h : n > 0) : (⟨0, h⟩ : Fin n).val = 0 := by
  rfl

-- LLM HELPER
lemma fin_val_last {n : Nat} (h : n > 0) : 
  (⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ : Fin n).val = n - 1 := by
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
  simp [linspace]
  constructor
  · -- First element is always start
    simp [vector_get_ofFn]
    split_ifs with h1
    · rfl
    · simp [toFloat_zero, zero_div]
      ring
  constructor
  · -- Special case: when num = 1
    intro h1 i
    simp [vector_get_ofFn]
    rw [if_pos h1]
  constructor
  · -- General case: when num > 1
    intro h1
    constructor
    · -- Last element is stop
      simp [vector_get_ofFn]
      rw [if_neg (ne_of_gt h1)]
      simp [fin_val_last]
      ring
    constructor
    · -- All elements follow the linear formula
      intro i
      simp [vector_get_ofFn]
      rw [if_neg (ne_of_gt h1)]
    · -- Consecutive elements have constant spacing
      intro i j hij
      simp [vector_get_ofFn]
      rw [if_neg (ne_of_gt h1), if_neg (ne_of_gt h1)]
      ring
  constructor
  · -- Monotonicity: start < stop case
    intro hlt i j hij
    simp [vector_get_ofFn]
    split_ifs with h1 h2 h3
    · cases h1; cases h2; exact False.elim (ne_of_gt hij rfl)
    · cases h1; exact hlt
    · cases h2; exact hlt
    · apply Float.add_lt_add_left
      apply Float.mul_lt_mul_of_pos_right
      · simp only [Nat.cast_lt]
        exact hij
      · simp only [Float.div_pos_iff]
        constructor
        · exact Float.sub_pos.mpr hlt
        · simp only [Nat.cast_pos]
          exact Nat.sub_pos_of_lt h1
  constructor
  · -- Monotonicity: start > stop case
    intro hgt i j hij
    simp [vector_get_ofFn]
    split_ifs with h1 h2 h3
    · cases h1; cases h2; exact False.elim (ne_of_gt hij rfl)
    · cases h1; exact hgt
    · cases h2; exact hgt
    · apply Float.add_lt_add_left
      apply Float.mul_lt_mul_of_neg_right
      · simp only [Nat.cast_lt]
        exact hij
      · simp only [Float.div_neg_iff]
        constructor
        · exact Float.sub_neg.mpr hgt
        · simp only [Nat.cast_pos]
          exact Nat.sub_pos_of_lt h1
  constructor
  · -- Equality case
    intro heq i
    simp [vector_get_ofFn]
    split_ifs with h1
    · exact heq
    · simp [heq]
      ring
  constructor
  · -- Bounds property
    intro i
    simp [vector_get_ofFn]
    split_ifs with h1
    · constructor
      · exact Float.min_le_left start stop
      · exact Float.le_max_left start stop
    · constructor <;> simp
  constructor
  · -- Linear interpolation property
    intro h1 i
    simp [vector_get_ofFn]
    rw [if_neg (ne_of_gt h1)]
    ring
  · -- Reverse symmetry
    intro h1 i hi hj
    simp [vector_get_ofFn]
    rw [if_neg (ne_of_gt h1)]
    ring