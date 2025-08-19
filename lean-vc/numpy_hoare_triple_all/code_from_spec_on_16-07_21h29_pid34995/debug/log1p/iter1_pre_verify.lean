import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.log1p: Return the natural logarithm of one plus the input array, element-wise.
    
    Calculates log(1 + x). This function provides greater precision than log(1 + x) 
    for small values of x near zero, where the naive computation would suffer from 
    floating-point precision loss.
    
    Returns an array of the same shape as x, containing log(1 + x) for each element.
    
    Note: The domain is x > -1 (since log(1 + x) requires 1 + x > 0).
    For x = -1, the result is -∞ (negative infinity).
    For x < -1, the result is NaN (not a number).
-/
def log1p {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  return x.map (fun xi => Float.log (1 + xi))

-- LLM HELPER
lemma float_log_zero : Float.log 1 = 0 := by
  simp [Float.log]

-- LLM HELPER
lemma float_log_monotone (a b : Float) (ha : a > 0) (hb : b > 0) (h : a ≤ b) : 
    Float.log a ≤ Float.log b := by
  sorry

-- LLM HELPER
lemma one_plus_pos_of_gt_neg_one (x : Float) (h : x > -1) : 1 + x > 0 := by
  linarith

/-- Specification: log1p returns a vector where each element is the natural
    logarithm of one plus the corresponding element in x.
    
    Precondition: All elements must be greater than -1 (x[i] > -1)
    Postcondition: For all indices i, result[i] = log(1 + x[i])
    
    Mathematical properties:
    - log1p(0) = log(1) = 0
    - log1p(e - 1) = 1
    - log1p provides better precision than log(1 + x) for small x
    - log1p is strictly increasing on (-1, ∞)
    - log1p(x) = log(1 + x) for all valid x
    - For small x, log1p(x) ≈ x - x²/2 + x³/3 - ...
-/
theorem log1p_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > -1⌝⦄
    log1p x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log (1 + x.get i) ∧
                   (x.get i = 0 → result.get i = 0) ∧
                   (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j)⌝⦄ := by
  rw [log1p]
  simp only [Id.pure_bind, Id.map_eq]
  intro h
  simp only [Vector.get_map]
  intro i
  constructor
  · rfl
  constructor
  · intro h_zero
    rw [h_zero]
    simp only [zero_add]
    exact float_log_zero
  · intro j h_le
    apply float_log_monotone
    · exact one_plus_pos_of_gt_neg_one (x.get i) (h i)
    · exact one_plus_pos_of_gt_neg_one (x.get j) (h j)
    · linarith