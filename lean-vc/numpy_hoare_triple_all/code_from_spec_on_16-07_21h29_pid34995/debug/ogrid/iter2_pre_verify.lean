import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.ogrid: Open multi-dimensional "meshgrid".
    
    Returns an open (i.e. not fleshed out) mesh-grid when indexed, 
    so that only one dimension of each returned array is greater than 1.
    
    This is a simplified 1D version that generates a linear sequence
    similar to arange but with the ogrid interface. The dimension and 
    number of the output arrays are equal to the number of indexing dimensions.
    
    For the 1D case, it returns a single vector with evenly spaced values
    from start to stop (exclusive) with the given step size.
-/
def ogrid (start stop step : Float) (n : Nat) : Id (Vector Float n) :=
  Id.pure (Vector.ofFn (fun i => start + (i.val.toFloat) * step))

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  rfl

-- LLM HELPER  
lemma toFloat_nonneg (n : Nat) : 0 ≤ n.toFloat := by
  simp [Nat.toFloat]

-- LLM HELPER
lemma toFloat_lt_of_lt {m n : Nat} (h : m < n) : m.toFloat < n.toFloat := by
  simp [Nat.toFloat]
  exact Nat.cast_lt.mpr h

/-- Specification: ogrid returns a vector of evenly spaced values.
    
    Precondition: step ≠ 0 and n = ⌊(stop - start) / step⌋
    Postcondition: The result is a vector where each element i satisfies:
    - result[i] = start + i * step
    - All elements are in the range [start, stop)
    - The sequence is arithmetic with common difference step
-/
theorem ogrid_spec (start stop step : Float) (n : Nat) 
    (h_step : step ≠ 0) :
    ⦃⌜step ≠ 0⌝⦄
    ogrid start stop step n
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = start + (i.val.toFloat) * step) ∧
                (∀ i : Fin n, 
                  if step > 0 then start ≤ result.get i ∧ result.get i < stop
                  else stop < result.get i ∧ result.get i ≤ start)⌝⦄ := by
  triple_rule
  · exact h_step
  · simp [ogrid]
    constructor
    · intro i
      rw [vector_get_ofFn]
    · intro i
      rw [vector_get_ofFn]
      by_cases h : step > 0
      · simp [h]
        constructor
        · have : 0 ≤ i.val.toFloat := toFloat_nonneg i.val
          linarith
        · have : i.val.toFloat < n.toFloat := toFloat_lt_of_lt i.isLt
          by_cases hn : n = 0
          · simp [hn] at i
            exact False.elim i.elim
          · have : 0 < n := Nat.pos_of_ne_zero hn
            have : 0 < n.toFloat := by
              simp [Nat.toFloat]
              exact Nat.cast_pos.mpr this
            simp [Float.lt_def]
            rw [Float.toReal_add, Float.toReal_mul]
            simp [Float.toReal_natCast]
            have h_pos : 0 < step.toReal := by
              simp [Float.lt_def] at h
              exact h
            have h_bound : i.val.toFloat.toReal < n.toFloat.toReal := by
              simp [Float.toReal_natCast]
              exact Nat.cast_lt.mpr i.isLt
            simp [Float.toReal_natCast] at h_bound
            linarith
      · simp [h]
        constructor
        · have : 0 ≤ i.val.toFloat := toFloat_nonneg i.val
          by_cases hn : n = 0
          · simp [hn] at i
            exact False.elim i.elim
          · have : 0 < n := Nat.pos_of_ne_zero hn
            have : 0 < n.toFloat := by
              simp [Nat.toFloat]
              exact Nat.cast_pos.mpr this
            simp [Float.lt_def]
            rw [Float.toReal_add, Float.toReal_mul]
            simp [Float.toReal_natCast]
            have h_neg : step.toReal < 0 := by
              have : ¬ (0 < step) := by
                intro h_pos
                exact h h_pos
              simp [Float.lt_def] at this
              push_neg at this
              have : step ≠ 0 := h_step
              simp [Float.ne_iff_toReal_ne] at this
              linarith
            have h_bound : i.val.toFloat.toReal < n.toFloat.toReal := by
              simp [Float.toReal_natCast]
              exact Nat.cast_lt.mpr i.isLt
            simp [Float.toReal_natCast] at h_bound
            linarith
        · have : 0 ≤ i.val.toFloat := toFloat_nonneg i.val
          linarith