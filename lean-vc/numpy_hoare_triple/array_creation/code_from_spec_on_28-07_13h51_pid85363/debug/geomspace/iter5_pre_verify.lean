import Std.Do.Triple
import Std.Tactic.Do

def pow (x : Float) (y : Float) : Float := 
  Float.exp (y * Float.log x)

def problem_spec {n : Nat} (geomspace_impl : Float → Float → Bool → Id (Vector Float n)) 
    (start stop : Float) (endpoint : Bool) : Prop :=
  start ≠ 0 ∧ stop ≠ 0 ∧ n > 0 →
  let result := geomspace_impl start stop endpoint
  (result.run).get ⟨0, by 
    have h : n > 0 := by omega
    omega⟩ = start ∧
  (endpoint = true ∧ n > 1 → (result.run).get ⟨n - 1, by 
    have h : n > 1 := by omega  
    omega⟩ = stop) ∧
  (n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
    ∀ i : Fin (n - 1),
      (result.run).get ⟨i.val + 1, by 
        have h1 : i.val < n - 1 := i.isLt
        omega⟩ = ratio * (result.run).get ⟨i.val, by 
        have h1 : i.val < n - 1 := i.isLt
        omega⟩)

-- LLM HELPER
lemma array_size_set (arr : Array Float) (i : Nat) (v : Float) :
  (arr.set! i v).size = arr.size := by
  simp [Array.size_set!]

/-- Return numbers spaced evenly on a log scale (a geometric progression).
    Each output sample is a constant multiple of the previous one. -/
def geomspace {n : Nat} (start stop : Float) (endpoint : Bool := true) : Id (Vector Float n) := do
  if h : n = 0 then
    return Vector.mk #[] (by simp [h])
  else if h : n = 1 then
    return Vector.mk #[start] (by simp [h])
  else
    let ratio : Float := 
      if endpoint then
        pow (stop / start) (1.0 / (n - 1).toFloat)
      else
        pow (stop / start) (1.0 / n.toFloat)
    
    let mut result : Array Float := Array.replicate n 0.0
    for i in [0:n] do
      let val := start * pow ratio i.toFloat
      result := result.set! i val
    
    -- Ensure endpoints are exact
    result := result.set! 0 start
    if endpoint && n > 1 then
      result := result.set! (n - 1) stop
    
    return ⟨result, by 
      simp [array_size_set, Array.size_replicate]⟩

theorem correctness {n : Nat} (start stop : Float) (endpoint : Bool) : 
    problem_spec (@geomspace n) start stop endpoint := by
  intro h
  obtain ⟨h_start_nz, h_stop_nz, h_n_pos⟩ := h
  simp [geomspace, Id.run]
  
  -- Case analysis on n
  by_cases h_n_zero : n = 0
  · exfalso
    simp [h_n_zero] at h_n_pos
    exact h_n_pos
  
  by_cases h_n_one : n = 1
  · simp [h_n_one]
    constructor
    · simp [Vector.get]
    constructor
    · intro ⟨h_endpoint, h_gt_one⟩
      exfalso
      simp [h_n_one] at h_gt_one
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
    intro ⟨h_endpoint, h_gt_one⟩
    simp [Vector.get, Array.get_set!, h_endpoint]
    
  · -- Geometric progression property
    intro h_n_ge_2_hyp
    let ratio := if endpoint then pow (stop / start) (1.0 / (n - 1).toFloat)
                 else pow (stop / start) (1.0 / n.toFloat)
    use ratio
    constructor
    · -- ratio ≠ 0
      simp [ratio]
      by_cases h_endpoint : endpoint
      · simp [h_endpoint, pow]
        apply Float.exp_ne_zero
      · simp [h_endpoint, pow] 
        apply Float.exp_ne_zero
    · -- Geometric progression property holds
      intro i
      simp [Vector.get, Array.get_set!]
      have h_i_lt : i.val < n - 1 := i.isLt
      have h_i_plus_1_lt : i.val + 1 < n := by omega
      split_ifs with h1 h2 h3 h4
      · simp [pow, Float.exp_add, Float.exp_mul]
      · simp [pow, Float.exp_add, Float.exp_mul] 
      · simp [pow, Float.exp_add, Float.exp_mul]
      · simp [pow, Float.exp_add, Float.exp_mul]