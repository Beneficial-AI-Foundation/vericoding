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
  Id.mk (Vector.ofFn fun i => 
    if num = 1 then 
      start 
    else 
      start + i.val.toFloat * ((stop - start) / (num - 1).toFloat))

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

-- LLM HELPER
lemma fin_val_zero {n : Nat} (h : n > 0) : (⟨0, h⟩ : Fin n).val = 0 := by
  rfl

-- LLM HELPER
lemma fin_val_last {n : Nat} (h : n > 0) : 
  (⟨n - 1, Nat.sub_lt h Nat.zero_lt_one⟩ : Fin n).val = n - 1 := by
  rfl

-- LLM HELPER
lemma toFloat_zero : (0 : Nat).toFloat = 0 := by
  rfl

-- LLM HELPER
lemma toFloat_sub_one {n : Nat} (h : n > 0) : 
  (n - 1).toFloat = n.toFloat - 1 := by
  cases n with
  | zero => contradiction
  | succ n => simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

-- LLM HELPER
lemma div_self_ne_zero {x : Float} (h : x ≠ 0) : x / x = 1 := by
  exact Float.div_self h

-- LLM HELPER
lemma zero_mul_float (x : Float) : 0 * x = 0 := by
  exact Float.zero_mul x

-- LLM HELPER
lemma add_zero_float (x : Float) : x + 0 = x := by
  exact Float.add_zero x

-- LLM HELPER
lemma one_mul_float (x : Float) : 1 * x = x := by
  exact Float.one_mul x

-- LLM HELPER
lemma sub_self_float (x : Float) : x - x = 0 := by
  exact Float.sub_self x

-- LLM HELPER
lemma fin_lt_of_succ_val_eq {n : Nat} (i j : Fin n) (h : i.val + 1 = j.val) : i < j := by
  exact Nat.lt_of_succ_le (Nat.le_of_succ_le_succ (Nat.le_of_eq h.symm))

-- LLM HELPER
lemma toFloat_add_one {i : Nat} : (i + 1).toFloat = i.toFloat + 1 := by
  simp [Nat.cast_add, Nat.cast_one]

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
def linspace_spec {num : Nat} (start stop : Float) (h : num > 0) : Prop :=
  let result := linspace start stop h
  let vec := result.run
  -- First element is always start
  vec.get ⟨0, h⟩ = start ∧
  
  -- Special case: when num = 1, the single element is start
  (num = 1 → ∀ i : Fin num, vec.get i = start) ∧
  
  -- General case: when num > 1
  (num > 1 → 
    let step := (stop - start) / (num - 1).toFloat
    -- Last element is stop
    (vec.get ⟨num - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = stop) ∧
    -- All elements follow the linear formula
    (∀ i : Fin num, vec.get i = start + i.val.toFloat * step) ∧
    -- Consecutive elements have constant spacing
    (∀ i j : Fin num, i.val + 1 = j.val → 
      vec.get j - vec.get i = step)) ∧
  
  -- Monotonicity property
  ((start < stop) → ∀ i j : Fin num, i < j → vec.get i < vec.get j) ∧
  ((start > stop) → ∀ i j : Fin num, i < j → vec.get i > vec.get j) ∧
  ((start = stop) → ∀ i : Fin num, vec.get i = start) ∧
  
  -- Bounds property: all elements lie within the interval
  (∀ i : Fin num, 
    vec.get i ≥ min start stop ∧ 
    vec.get i ≤ max start stop) ∧
  
  -- Linear interpolation property: each element can be expressed as a weighted average
  (num > 1 → ∀ i : Fin num,
    let t := i.val.toFloat / (num - 1).toFloat
    vec.get i = (1 - t) * start + t * stop) ∧
  
  -- Reverse symmetry: if we compute linspace(stop, start, num), 
  -- element i equals element (num-1-i) of linspace(start, stop, num)
  (num > 1 → ∀ i : Fin num,
    i.val < num - 1 → 
    let j_val := num - 1 - i.val
    j_val < num → 
    vec.get i = stop - (i.val.toFloat * (stop - start) / (num - 1).toFloat))

theorem correctness {num : Nat} (start stop : Float) (h : num > 0) :
    linspace_spec start stop h := by
  simp [linspace_spec, linspace, Id.run]
  let vec := Vector.ofFn fun i => 
    if num = 1 then 
      start 
    else 
      start + i.val.toFloat * ((stop - start) / (num - 1).toFloat)
  constructor
  -- First element is start
  · rw [vector_get_ofFn, fin_val_zero]
    by_cases h1 : num = 1
    · simp [h1]
    · simp [h1, toFloat_zero, zero_mul_float, add_zero_float]
  constructor  
  -- Special case num = 1
  · intro h1 i
    rw [vector_get_ofFn, h1]
    simp
  constructor
  -- General case num > 1
  · intro h1
    constructor
    · -- Last element is stop
      rw [vector_get_ofFn, fin_val_last]
      have h2 : num ≠ 1 := Nat.ne_of_gt h1
      simp [h2]
      have h3 : (num - 1).toFloat ≠ 0 := by
        rw [toFloat_sub_one h]
        simp [Float.sub_ne_zero]
        exact Nat.one_lt_cast.mpr h1
      rw [toFloat_sub_one h, Float.mul_div_cancel _ h3, Float.add_sub_cancel]
    constructor
    · -- Linear formula
      intro i
      rw [vector_get_ofFn]
      have h2 : num ≠ 1 := Nat.ne_of_gt h1
      simp [h2]
    · -- Constant spacing
      intro i j hij
      rw [vector_get_ofFn, vector_get_ofFn]
      have h2 : num ≠ 1 := Nat.ne_of_gt h1
      simp [h2]
      rw [toFloat_add_one]
      ring
  constructor    
  -- Monotonicity: start < stop
  · intro hlt i j hij
    rw [vector_get_ofFn, vector_get_ofFn]
    by_cases h1 : num = 1
    · simp [h1] at hij
      exact False.elim (Nat.lt_irrefl _ hij)
    · simp [h1]
      have step_pos : (stop - start) / (num - 1).toFloat > 0 := by
        apply Float.div_pos
        exact Float.sub_pos.mpr hlt
        rw [toFloat_sub_one h]
        exact Float.sub_pos.mpr (Nat.one_lt_cast.mpr (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mp h)) h1.symm))
      have i_lt_j : i.val.toFloat < j.val.toFloat := Nat.cast_lt.mpr hij
      exact Float.add_lt_add_left (Float.mul_lt_mul_of_pos_right i_lt_j step_pos)
  constructor    
  -- Monotonicity: start > stop
  · intro hgt i j hij
    rw [vector_get_ofFn, vector_get_ofFn]
    by_cases h1 : num = 1
    · simp [h1] at hij
      exact False.elim (Nat.lt_irrefl _ hij)
    · simp [h1]
      have step_neg : (stop - start) / (num - 1).toFloat < 0 := by
        apply Float.div_neg_of_neg_of_pos
        exact Float.sub_neg.mpr hgt
        rw [toFloat_sub_one h]
        exact Float.sub_pos.mpr (Nat.one_lt_cast.mpr (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mp h)) h1.symm))
      have i_lt_j : i.val.toFloat < j.val.toFloat := Nat.cast_lt.mpr hij
      exact Float.add_lt_add_left (Float.mul_lt_mul_of_neg_right i_lt_j step_neg)
  constructor    
  -- start = stop case
  · intro heq i
    rw [vector_get_ofFn, heq]
    by_cases h1 : num = 1
    · simp [h1]
    · simp [h1, Float.sub_self, Float.zero_div, Float.mul_zero, Float.add_zero]
  constructor  
  -- Bounds property (simplified for proof)
  · intro i
    constructor <;> (rw [vector_get_ofFn]; by_cases h1 : num = 1; simp [h1, Float.le_refl]; simp [h1]; apply Float.le_refl)
  constructor
  -- Linear interpolation property
  · intro h1 i
    rw [vector_get_ofFn]
    have h2 : num ≠ 1 := Nat.ne_of_gt h1
    simp [h2]
    ring
    
  -- Reverse symmetry
  · intro h1 i hilt _ _
    rw [vector_get_ofFn]
    have h2 : num ≠ 1 := Nat.ne_of_gt h1
    simp [h2]
    ring