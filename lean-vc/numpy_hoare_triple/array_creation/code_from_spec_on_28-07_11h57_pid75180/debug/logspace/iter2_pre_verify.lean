import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def problem_spec {num : Nat} (logspace_fn : Float → Float → Bool → Float → Id (Vector Float num)) 
    (start stop : Float) (endpoint : Bool) (base : Float) 
    (h_base_pos : base > 0) (h_base_ne_one : base ≠ 1) (h_num_pos : num > 0) : Prop :=
  ⦃⌜base > 0 ∧ base ≠ 1 ∧ num > 0⌝⦄
  logspace_fn start stop endpoint base
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
  ⌝⦄

/-- Return numbers spaced evenly on a log scale.
    
    Creates a vector of `num` samples where each element is computed as:
    - When endpoint=true: base^(start + i * (stop - start) / (num - 1)) for i in 0..num-1
    - When endpoint=false: base^(start + i * (stop - start) / num) for i in 0..num-1
    
    The samples are evenly spaced in log space, meaning the exponents form an arithmetic sequence.
-/
def logspace {num : Nat} (start stop : Float) (endpoint : Bool) (base : Float) : Id (Vector Float num) :=
  let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
              else (stop - start) / num.toFloat
  Vector.ofFn (fun i => base ^ (start + i.val.toFloat * step))

-- LLM HELPER
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

-- LLM HELPER  
lemma pow_pos {x : Float} {y : Float} (hx : x > 0) : x ^ y > 0 := by
  simp [Float.pow_pos hx]

theorem correctness {num : Nat} (start stop : Float) (endpoint : Bool) (base : Float) 
    (h_base_pos : base > 0) (h_base_ne_one : base ≠ 1) (h_num_pos : num > 0) :
    problem_spec logspace start stop endpoint base h_base_pos h_base_ne_one h_num_pos := by
  simp only [problem_spec, logspace, Triple.bind_iff, Triple.pure_iff]
  constructor
  · exact ⟨h_base_pos, h_base_ne_one, h_num_pos⟩
  constructor
  · intro h
    constructor
    · intro i
      simp [vector_ofFn_get]
    constructor
    · simp [vector_ofFn_get]
      simp [Nat.cast_zero, mul_zero, add_zero]
    constructor
    · intro h_endpoint h_num_gt_one
      simp [vector_ofFn_get]
      have : (num - 1).toFloat = num.toFloat - 1 := by
        simp [Nat.cast_sub, Nat.one_le_iff_ne_zero]
        omega
      simp [this]
      ring_nf
      congr 1
      simp [h_endpoint, h_num_gt_one]
      field_simp
      ring
    · intro i
      simp [vector_ofFn_get]
      exact pow_pos h_base_pos
  · intro result h
    exact result