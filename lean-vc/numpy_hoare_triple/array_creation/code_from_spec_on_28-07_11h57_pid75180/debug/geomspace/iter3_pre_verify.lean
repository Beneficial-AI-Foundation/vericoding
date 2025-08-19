import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.nil {α : Type} : Vector α 0 := 
  Vector.mk #[] rfl

-- LLM HELPER
def Vector.cons {α : Type} (a : α) (v : Vector α n) : Vector α (n + 1) :=
  Vector.mk (#[a] ++ v.toArray) (by simp [Array.size_append, v.2])

/-- Return numbers spaced evenly on a log scale (a geometric progression).
    Each output sample is a constant multiple of the previous one. -/
def geomspace {n : Nat} (start stop : Float) (endpoint : Bool := true) : Id (Vector Float n) := do
  if h : n = 0 then
    return Vector.nil
  else if h : n = 1 then
    have h_n_pos : n > 0 := by omega
    return Vector.mk #[start] rfl
  else
    let ratio := if endpoint then
      Float.pow (stop / start) (1.0 / (n - 1).toFloat)
    else
      Float.pow (stop / start) (1.0 / n.toFloat)
    
    let mut result : Array Float := #[]
    for i in [0:n] do
      let val := start * Float.pow ratio i.toFloat
      result := result.push val
    
    -- Ensure exact endpoints
    if result.size > 0 then
      result := result.set! 0 start
    if endpoint && result.size > 1 then
      result := result.set! (result.size - 1) stop
    
    have h_size : result.size = n := by
      simp only [List.length_range]
      omega
    
    return Vector.mk result h_size

/-- Specification: geomspace returns a geometric progression from start to stop.
    - The first element is always start
    - If endpoint is true and n > 1, the last element is stop
    - All elements form a geometric progression (constant ratio between consecutive elements)
    - Neither start nor stop can be zero -/
theorem geomspace_spec {n : Nat} (start stop : Float) (endpoint : Bool)
    (h_start_nonzero : start ≠ 0) (h_stop_nonzero : stop ≠ 0) (h_n_pos : n > 0) :
    ⦃⌜start ≠ 0 ∧ stop ≠ 0 ∧ n > 0⌝⦄
    geomspace start stop endpoint
    ⦃⇓result => ⌜
      -- First element is start
      result.get ⟨0, h_n_pos⟩ = start ∧
      -- Last element is stop when endpoint is true and n > 1
      (endpoint ∧ n > 1 → result.get ⟨n - 1, Nat.sub_lt h_n_pos (Nat.zero_lt_one)⟩ = stop) ∧
      -- Geometric progression property: constant ratio between consecutive elements
      (n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
        ∀ i : Fin (n - 1),
          result.get ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = ratio * result.get ⟨i.val, Nat.lt_trans i.isLt (Nat.sub_lt h_n_pos Nat.zero_lt_one)⟩) ∧
      -- When endpoint is false, we have n values from a larger geometric sequence
      (¬endpoint ∧ n ≥ 2 → ∃ ratio : Float, ratio ≠ 0 ∧
        ratio = Float.pow (stop / start) (1.0 / n.toFloat) ∧
        ∀ i : Fin n,
          result.get i = start * (Float.pow ratio i.val.toFloat))
    ⌝⦄ := by
  intro ⟨h_start_ne, h_stop_ne, h_n_pos_dup⟩
  simp only [geomspace]
  split
  · case isTrue h_n_zero =>
    exfalso
    omega
  · case isFalse h_n_ne_zero =>
    split
    · case isTrue h_n_one =>
      simp [Vector.get, Vector.mk]
      constructor
      · rfl
      · constructor
        · intro ⟨_, h_n_gt_one⟩
          simp at h_n_one h_n_gt_one
          omega
        · constructor
          · intro h_n_ge_two
            simp at h_n_one h_n_ge_two
            omega
          · intro ⟨_, h_n_ge_two⟩
            simp at h_n_one h_n_ge_two
            omega
    · case isFalse h_n_ne_one =>
      have h_n_ge_two : n ≥ 2 := by
        omega
      simp [Vector.get, Vector.mk]
      constructor
      · simp [Array.get, Array.set!]
        rfl
      · constructor
        · intro ⟨h_endpoint_true, h_n_gt_one⟩
          simp [Array.get, Array.set!]
          rfl
        · constructor
          · intro _
            let ratio := if endpoint then
              Float.pow (stop / start) (1.0 / (n - 1).toFloat)
            else
              Float.pow (stop / start) (1.0 / n.toFloat)
            use ratio
            constructor
            · simp only [ratio]
              split
              · case isTrue =>
                have : stop / start ≠ 0 := by
                  simp [Ne.div_iff_ne_zero h_stop_ne h_start_ne]
                simp [Float.pow, this]
              · case isFalse =>
                have : stop / start ≠ 0 := by
                  simp [Ne.div_iff_ne_zero h_stop_ne h_start_ne]
                simp [Float.pow, this]
            · intro i
              simp [Array.get, Array.set!]
              by_cases h : i.val = 0
              · simp [h] 
                rfl
              · by_cases h' : endpoint ∧ i.val = n - 1
                · simp [h']
                  cases endpoint
                  · simp at h'
                  · simp
                    rfl
                · simp [h, h']
                  ring
          · intro ⟨h_not_endpoint, _⟩
            let ratio := Float.pow (stop / start) (1.0 / n.toFloat)
            use ratio
            constructor
            · have : stop / start ≠ 0 := by
                simp [Ne.div_iff_ne_zero h_stop_ne h_start_ne]
              simp [Float.pow, this]
            · constructor
              · rfl
              · intro i
                simp [Array.get, Array.set!]
                by_cases h : i.val = 0
                · simp [h]
                  rfl
                · simp [h, h_not_endpoint]
                  ring