import Std.Do.Triple
import Std.Tactic.Do

def pow (x : Float) (y : Float) : Float := 
  Float.exp (y * Float.log x)

def problem_spec {n : Nat} (geomspace_impl : Float → Float → Bool → Id (Vector Float n)) 
    (start stop : Float) (endpoint : Bool) : Prop :=
  start ≠ 0 ∧ stop ≠ 0 ∧ n > 0 →
  let result := geomspace_impl start stop endpoint
  (result.run).get ⟨0, by 
    have h : n > 0 := by sorry
    exact Nat.pos_iff_ne_zero.mp h⟩ = start ∧
  (endpoint = true ∧ n > 1 → (result.run).get ⟨n - 1, by 
    have h : n > 1 := by sorry  
    exact Nat.sub_pos_of_lt h⟩ = stop) ∧
  (n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
    ∀ i : Fin (n - 1),
      (result.run).get ⟨i.val + 1, by 
        have h1 : i.val < n - 1 := i.isLt
        exact Nat.lt_trans (Nat.lt_succ_self i.val) (Nat.sub_pos_of_lt (by linarith))⟩ = ratio * (result.run).get ⟨i.val, by 
        have h1 : i.val < n - 1 := i.isLt
        exact Nat.lt_trans h1 (Nat.sub_pos_of_lt (by linarith))⟩)

-- LLM HELPER
lemma array_size_setIfInBounds (arr : Array Float) (i : Nat) (v : Float) :
  (arr.setIfInBounds i v).size = arr.size := by
  simp [Array.setIfInBounds]
  split
  · simp [Array.size_set!]
  · rfl

-- LLM HELPER
lemma list_foldl_size (arr : Array Float) (l : List Nat) (f : Array Float → Nat → Array Float) :
  (List.foldl f arr l).size = arr.size := by
  induction l generalizing arr with
  | nil => rfl
  | cons h t ih => 
    simp [List.foldl]
    apply ih

-- LLM HELPER
lemma array_get_setIfInBounds_same (arr : Array Float) (i : Nat) (v : Float) (h : i < arr.size) :
  (arr.setIfInBounds i v)[i]'(by simp [Array.size_setIfInBounds, h]) = v := by
  simp [Array.setIfInBounds, h, Array.get_set!]

-- LLM HELPER
lemma pow_ne_zero (x : Float) (y : Float) : x ≠ 0 → pow x y ≠ 0 := by
  intro h
  simp [pow]
  apply Float.exp_ne_zero

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
    for i in List.range' 0 n do
      let val := start * pow ratio i.toFloat
      result := result.setIfInBounds i val
    
    -- Ensure endpoints are exact
    result := result.setIfInBounds 0 start
    if endpoint && n > 1 then
      result := result.setIfInBounds (n - 1) stop
    
    return ⟨result, by 
      simp only [Array.size_setIfInBounds, Array.size_replicate]
      rfl⟩

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
    simp [Vector.get]
    rfl
    
  constructor
  · -- Last element is stop when endpoint is true and n > 1
    intro ⟨h_endpoint, h_gt_one⟩
    simp [Vector.get, h_endpoint]
    rfl
    
  · -- Geometric progression property
    intro h_n_ge_2_hyp
    let ratio := if endpoint then pow (stop / start) (1.0 / (n - 1).toFloat)
                 else pow (stop / start) (1.0 / n.toFloat)
    use ratio
    constructor
    · -- ratio ≠ 0
      simp [ratio]
      split
      · apply pow_ne_zero
        linarith [h_start_nz, h_stop_nz]
      · apply pow_ne_zero
        linarith [h_start_nz, h_stop_nz]
    · -- Geometric progression property holds
      intro i
      simp [Vector.get]
      rfl