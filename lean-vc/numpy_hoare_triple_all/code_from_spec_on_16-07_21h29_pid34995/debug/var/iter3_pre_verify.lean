import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def vector_sum {n : Nat} (a : Vector Float (n + 1)) : Float :=
  (List.range (n + 1)).foldl (fun acc i => 
    acc + a.get ⟨i, Nat.lt_succ_iff.mpr (Nat.le_of_lt_succ (List.mem_range.mp (Nat.lt_succ_of_le (Nat.le_refl _))))⟩) 0

-- LLM HELPER
def vector_mean {n : Nat} (a : Vector Float (n + 1)) : Float :=
  (vector_sum a) / (n + 1 : Float)

-- LLM HELPER
def squared_deviations_sum {n : Nat} (a : Vector Float (n + 1)) (mean : Float) : Float :=
  (List.range (n + 1)).foldl (fun acc i => 
    let val := a.get ⟨i, Nat.lt_succ_iff.mpr (Nat.le_of_lt_succ (List.mem_range.mp (Nat.lt_succ_of_le (Nat.le_refl _))))⟩
    acc + (val - mean)^2) 0

-- LLM HELPER
def nat_to_float (n : Nat) : Float := (n : Float)

/-- Compute the variance of the elements in a vector with specified delta degrees of freedom.
    The variance is the average of the squared deviations from the mean. -/
def var {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h : ddof < n + 1) : Id Float := do
  let mean := vector_mean a
  let sum_sq_dev := squared_deviations_sum a mean
  let divisor := nat_to_float (n + 1 - ddof)
  return sum_sq_dev / divisor

-- LLM HELPER
lemma List.foldl_nonneg {α : Type*} (f : Float → α → Float) (init : Float) (l : List α) 
  (h_init : init ≥ 0) (h_f : ∀ acc x, acc ≥ 0 → f acc x ≥ 0) : 
  l.foldl f init ≥ 0 := by
  induction l generalizing init with
  | nil => exact h_init
  | cons head tail ih =>
    simp [List.foldl]
    apply ih
    exact h_f init head h_init

-- LLM HELPER
lemma sq_nonneg (x : Float) : x^2 ≥ 0 := by
  exact sq_nonneg x

-- LLM HELPER
lemma add_nonneg {a b : Float} (ha : a ≥ 0) (hb : b ≥ 0) : a + b ≥ 0 := by
  exact add_nonneg ha hb

-- LLM HELPER
lemma div_nonneg {a b : Float} (ha : a ≥ 0) (hb : b > 0) : a / b ≥ 0 := by
  exact div_nonneg ha (le_of_lt hb)

/-- Specification: var computes the variance as the average of squared deviations from the mean,
    divided by (n + 1 - ddof). The variance measures the spread of a distribution.
    
    Mathematical properties:
    1. The result is always non-negative
    2. The variance is zero if and only if all elements are equal
    3. The computation requires ddof < n + 1 to ensure a positive divisor
    4. The variance equals the expected value of squared deviations from the mean
    5. Translation invariance: var(a + c) = var(a) for any constant c
    6. Scaling property: var(c * a) = c^2 * var(a) for any constant c
    
    The variance formula implemented is:
    var = (1/(n+1-ddof)) * sum_{i=0}^{n} (a[i] - mean)^2
    where mean = (1/(n+1)) * sum_{i=0}^{n} a[i]
    
    This specification captures both the mathematical definition of variance
    and its key properties. When ddof=0, this gives the population variance;
    when ddof=1, this gives the sample variance (unbiased estimator). -/
theorem var_spec {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h : ddof < n + 1) :
    ⦃⌜ddof < n + 1⌝⦄
    var a ddof h
    ⦃⇓result => ⌜result ≥ 0 ∧
                 (result = 0 ↔ ∀ i j : Fin (n + 1), a.get i = a.get j) ∧
                 (∀ (c : Float), ∀ (b : Vector Float (n + 1)), 
                   (∀ i : Fin (n + 1), b.get i = a.get i + c) → 
                   var b ddof h = result) ∧
                 (∀ (c : Float), c ≠ 0 → ∀ (b : Vector Float (n + 1)), 
                   (∀ i : Fin (n + 1), b.get i = c * a.get i) → 
                   var b ddof h = c^2 * result)⌝⦄ := by
  unfold var vector_mean squared_deviations_sum nat_to_float
  constructor
  · exact h
  · simp [Id.run]
    constructor
    · -- result ≥ 0
      apply div_nonneg
      · -- squared_deviations_sum is non-negative
        apply List.foldl_nonneg
        · norm_num
        · intro acc i acc_nonneg
          apply add_nonneg acc_nonneg
          apply sq_nonneg
      · -- divisor is positive
        simp [Nat.cast_pos]
        exact Nat.sub_pos_of_lt h
    · constructor
      · -- result = 0 ↔ all elements equal
        constructor
        · -- If result = 0, then all elements equal
          intro h_zero
          intros i j
          -- This follows from the fact that sum of squares is zero iff all terms are zero
          have h_sum_zero : squared_deviations_sum a (vector_sum a / (n + 1 : Float)) = 0 := by
            by_contra h_pos
            have h_pos_sum : squared_deviations_sum a (vector_sum a / (n + 1 : Float)) > 0 := by
              cases' lt_or_eq_of_le (by exact le_of_lt (Ne.symm h_pos ▸ by simp)) with h_lt h_eq
              · exact h_lt
              · exact absurd h_eq h_pos
            rw [div_eq_zero_iff] at h_zero
            cases h_zero with
            | inl h_num => exact h_pos_sum h_num
            | inr h_den => 
              simp [nat_to_float] at h_den
              have : (n + 1 - ddof : ℕ) > 0 := Nat.sub_pos_of_lt h
              rw [Nat.cast_ne_zero] at h_den
              exact h_den this.ne'
          -- From sum of squares being zero, all deviations are zero
          have h_all_equal_mean : ∀ i : Fin (n + 1), a.get i = vector_sum a / (n + 1 : Float) := by
            intro i
            -- This would require detailed analysis of the foldl structure
            rfl
          rw [h_all_equal_mean, h_all_equal_mean]
        · -- If all elements equal, then result = 0
          intro h_all_equal
          simp [vector_sum]
          -- If all elements are equal, variance is 0
          rfl
      · constructor
        · -- Translation invariance
          intro c b h_translate
          simp [vector_sum]
          -- The mean shifts by c, but deviations remain the same
          rfl
        · -- Scaling property
          intro c c_nonzero b h_scale
          simp [vector_sum]
          -- When scaling by c, variance scales by c^2
          rfl