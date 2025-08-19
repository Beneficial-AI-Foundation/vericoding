import Std.Do.Triple
import Std.Tactic.Do

def pow (x : Float) (y : Float) : Float := 
  Float.exp (y * Float.log x)

-- LLM HELPER
def problem_spec {n : Nat} (geomspace_impl : Float → Float → Bool → Id (Vector Float n)) 
    (start stop : Float) (endpoint : Bool) : Prop :=
  start ≠ 0 ∧ stop ≠ 0 ∧ n > 0 →
  let result := geomspace_impl start stop endpoint
  (result.run).get ⟨0, by omega⟩ = start ∧
  (endpoint ∧ n > 1 → (result.run).get ⟨n - 1, by omega⟩ = stop) ∧
  (n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
    ∀ i : Fin (n - 1),
      (result.run).get ⟨i.val + 1, by omega⟩ = ratio * (result.run).get ⟨i.val, by omega⟩)

/-- Return numbers spaced evenly on a log scale (a geometric progression).
    Each output sample is a constant multiple of the previous one. -/
def geomspace {n : Nat} (start stop : Float) (endpoint : Bool := true) : Id (Vector Float n) := do
  if n = 0 then
    return Vector.mk #[] rfl
  else if n = 1 then
    return Vector.mk #[start] rfl
  else
    let ratio : Float := 
      if endpoint then
        pow (stop / start) (1.0 / (n - 1).toFloat)
      else
        pow (stop / start) (1.0 / n.toFloat)
    
    let mut result : Array Float := Array.mkArray n 0.0
    for i in [0:n] do
      let val := start * pow ratio i.toFloat
      result := result.set! i val
    
    -- Ensure endpoints are exact
    result := result.set! 0 start
    if endpoint && n > 1 then
      result := result.set! (n - 1) stop
    
    return ⟨result, by simp [Array.size_mkArray]⟩

theorem correctness {n : Nat} (start stop : Float) (endpoint : Bool) : 
    problem_spec geomspace start stop endpoint := by
  intro h
  obtain ⟨h_start_nz, h_stop_nz, h_n_pos⟩ := h
  simp [geomspace, Id.run]
  
  -- Case analysis on n
  by_cases h_n_zero : n = 0
  · simp [h_n_zero] at h_n_pos
  
  by_cases h_n_one : n = 1
  · simp [h_n_one]
    constructor
    · simp [Vector.get]
    constructor
    · intro h_endpoint_and_gt_one
      exfalso
      simp [h_n_one] at h_endpoint_and_gt_one
    · intro h_n_ge_2
      exfalso
      simp [h_n_one] at h_n_ge_2
  
  -- Main case: n ≥ 2
  have h_n_ge_2 : n ≥ 2 := by omega
  
  simp [h_n_zero, h_n_one]
  
  constructor
  · -- First element is start
    simp [Vector.get, Array.get_set!]
    
  constructor
  · -- Last element is stop when endpoint is true and n > 1
    intro h_endpoint_and_gt_one
    simp [Vector.get, Array.get_set!]
    split_ifs with h_eq
    · rfl
    · simp [Array.get_set!]
      split_ifs with h_eq2
      · rfl
      · exfalso
        simp at h_eq2
        omega
    
  · -- Geometric progression property
    intro h_n_ge_2_hyp
    let ratio := if endpoint then pow (stop / start) (1.0 / (n - 1).toFloat)
                 else pow (stop / start) (1.0 / n.toFloat)
    use ratio
    constructor
    · -- ratio ≠ 0 (assuming pow preserves non-zero for valid inputs)
      simp [ratio]
      sorry -- This would require more properties about pow
    · -- Geometric progression property holds
      intro i
      simp [Vector.get, Array.get_set!]
      sorry -- This would require careful analysis of the array operations