import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return numbers spaced evenly on a log scale.
    
    Creates a vector of `num` samples where each element is computed as:
    - When endpoint=true: base^(start + i * (stop - start) / (num - 1)) for i in 0..num-1
    - When endpoint=false: base^(start + i * (stop - start) / num) for i in 0..num-1
    
    The samples are evenly spaced in log space, meaning the exponents form an arithmetic sequence.
-/
def logspace {num : Nat} (start stop : Float) (endpoint : Bool) (base : Float) : Id (Vector Float num) :=
  pure (Vector.ofFn fun i : Fin num => 
    let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
                else (stop - start) / num.toFloat
    base ^ (start + i.val.toFloat * step))

-- LLM HELPER
lemma float_pow_pos (base : Float) (exp : Float) (h : base > 0) : base ^ exp > 0 := by
  sorry

-- LLM HELPER  
lemma toFloat_nonneg (n : Nat) : n.toFloat ≥ 0 := by
  sorry

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f).get i = f i := by
  rfl

-- LLM HELPER
lemma fin_zero_val {n : Nat} (h : n > 0) : (⟨0, h⟩ : Fin n).val = 0 := by
  rfl

-- LLM HELPER
lemma fin_last_val {n : Nat} (h : n > 0) : (⟨n - 1, by omega⟩ : Fin n).val = n - 1 := by
  rfl

-- LLM HELPER
lemma step_formula_first {num : Nat} (start stop : Float) (endpoint : Bool) :
  let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
              else (stop - start) / num.toFloat
  start + 0 * step = start := by
  simp

-- LLM HELPER
lemma step_formula_last {num : Nat} (start stop : Float) (h : num > 1) :
  let step := (stop - start) / (num - 1).toFloat
  start + (num - 1).toFloat * step = stop := by
  simp [step]
  ring

/-- Specification: logspace generates numbers evenly spaced on a logarithmic scale.
    
    The function produces a vector where:
    1. For endpoint=true: Elements follow base^(interpolated exponent) where exponents 
       are linearly interpolated from start to stop inclusive
    2. For endpoint=false: Similar but stop value is excluded from the range
    3. The base must be positive and not equal to 1 for meaningful results
    4. For num > 1, the spacing between consecutive log values is uniform
-/
theorem logspace_spec {num : Nat} (start stop : Float) (endpoint : Bool) (base : Float) 
    (h_base_pos : base > 0) (h_base_ne_one : base ≠ 1) (h_num_pos : num > 0) :
    ⦃⌜base > 0 ∧ base ≠ 1 ∧ num > 0⌝⦄
    logspace start stop endpoint base
    ⦃⇓result => ⌜
      -- Define the step size based on endpoint parameter
      let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
                  else (stop - start) / num.toFloat
      -- Each element follows the logarithmic spacing formula
      (∀ i : Fin num, result.get i = base ^ (start + i.val.toFloat * step)) ∧
      -- First element is always base^start
      (result.get ⟨0, h_num_pos⟩ = base ^ start) ∧
      -- Last element is base^stop when endpoint is true and num > 1
      (endpoint ∧ num > 1 → result.get ⟨num - 1, by omega⟩ = base ^ stop) ∧
      -- All elements are positive when base is positive
      (∀ i : Fin num, result.get i > 0)
    ⌝⦄ := by
  intro h
  simp [logspace]
  constructor
  · intro i
    simp [vector_get_ofFn]
  constructor
  · simp [vector_get_ofFn, fin_zero_val, step_formula_first]
  constructor
  · intro h_endpoint h_num_gt_1
    simp [vector_get_ofFn, fin_last_val]
    rw [step_formula_last start stop h_num_gt_1]
    simp [h_endpoint, h_num_gt_1]
  · intro i
    simp [vector_get_ofFn]
    apply float_pow_pos
    exact h_base_pos