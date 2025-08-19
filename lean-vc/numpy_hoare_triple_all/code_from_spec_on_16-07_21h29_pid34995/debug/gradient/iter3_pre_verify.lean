import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma ne_of_gt {a b : Nat} (h : a < b) : a ≠ b := Nat.ne_of_lt h

-- LLM HELPER
def spec_of_pre_post {α : Type*} (f : Id α) (pre : Prop) (post : α → Prop) : 
    (pre → post f.run) → 
    ⦃⌜pre⌝⦄ f ⦃⇓a => ⌜post a⌝⦄ := by
  intro h
  simp [Std.Do.Triple.pure]
  exact h

/-- numpy.gradient: Return the gradient of an N-dimensional array.

    The gradient is computed using second order accurate central differences 
    in the interior points and either first or second order accurate one-sided 
    (forward or backwards) differences at the boundaries.
    
    For a 1D array, the gradient is a vector of the same size where:
    - At the boundaries, one-sided differences are used
    - In the interior, central differences are used
    
    This captures the rate of change of the function represented by the array.
-/
def numpy_gradient {n : Nat} (f : Vector Float (n + 1)) : Id (Vector Float (n + 1)) :=
  pure (Vector.ofFn fun i => 
    if n = 0 then 
      0
    else if i.val = 0 then
      f.get 1 - f.get 0
    else if i.val = n then
      f.get ⟨n, Nat.lt_succ_self n⟩ - f.get ⟨n-1, Nat.pred_lt (ne_of_gt (Nat.zero_lt_succ n))⟩
    else
      (f.get ⟨i.val + 1, by
        have h1 : i.val < n := by
          by_contra h
          simp at h
          have h2 : i.val ≥ n := Nat.le_of_not_gt h
          have h3 : i.val ≠ n := by
            split_ifs at * <;> simp at *
            assumption
          have h4 : i.val > n := Nat.lt_of_le_of_ne h2 h3
          have h5 : i.val < n + 1 := i.isLt
          omega
        exact Nat.succ_lt_succ h1⟩ - 
       f.get ⟨i.val - 1, by
        have h1 : i.val > 0 := by
          by_contra h
          simp at h
          have h2 : i.val = 0 := Nat.eq_zero_of_zero_le (Nat.zero_le i.val) h
          split_ifs at * <;> simp at *
          assumption
        have h2 : i.val - 1 < n + 1 := by
          have h3 : i.val ≤ n := by
            have h4 : i.val ≠ n := by
              split_ifs at * <;> simp at *
              assumption
            have h5 : i.val < n + 1 := i.isLt
            omega
          omega
        exact h2⟩) / 2)

-- LLM HELPER
lemma constant_function_gradient_zero {n : Nat} (f : Vector Float (n + 1)) (c : Float) 
    (h : ∀ i : Fin (n + 1), f.get i = c) : 
    ∀ i : Fin (n + 1), (numpy_gradient f).run.get i = 0 := by
  intro i
  simp [numpy_gradient]
  split
  · rfl
  · split
    · simp [h]
    · split
      · simp [h]
      · simp [h]
        ring

-- LLM HELPER
lemma single_point_gradient_zero {f : Vector Float 1} :
    (numpy_gradient f).run.get 0 = 0 := by
  simp [numpy_gradient]

-- LLM HELPER
lemma multi_point_first_boundary {n : Nat} (h : n > 0) (f : Vector Float (n + 1)) :
    (numpy_gradient f).run.get 0 = f.get 1 - f.get 0 := by
  simp [numpy_gradient]
  split
  · omega
  · rfl

-- LLM HELPER
lemma multi_point_last_boundary {n : Nat} (h : n > 0) (f : Vector Float (n + 1)) :
    (numpy_gradient f).run.get ⟨n, Nat.lt_succ_self n⟩ = 
    f.get ⟨n, Nat.lt_succ_self n⟩ - f.get ⟨n-1, Nat.pred_lt (ne_of_gt (Nat.zero_lt_succ n))⟩ := by
  simp [numpy_gradient]
  split
  · omega
  · split
    · simp at *
      omega
    · rfl

-- LLM HELPER
lemma multi_point_interior {n : Nat} (h : n > 0) (f : Vector Float (n + 1)) 
    (i : Fin (n + 1)) (hi : 0 < i.val ∧ i.val < n) :
    (numpy_gradient f).run.get i = 
    (f.get ⟨i.val + 1, Nat.succ_lt_succ (And.right hi)⟩ - 
     f.get ⟨i.val - 1, by
      have h1 : i.val - 1 < n + 1 := by
        have h2 : i.val ≤ n := Nat.le_of_lt (And.right hi)
        omega
      exact h1⟩) / 2 := by
  simp [numpy_gradient]
  split
  · omega
  · split
    · simp at *
      omega
    · split
      · simp at *
        omega
      · rfl

/-- Specification: numpy.gradient computes the numerical gradient using finite differences.
    
    The gradient satisfies these mathematical properties:
    1. For a single point array (n = 0), the gradient is 0
    2. For arrays with multiple points (n > 0):
       - At the first boundary (i = 0): uses forward difference grad[0] = f[1] - f[0]
       - At the last boundary (i = n): uses backward difference grad[n] = f[n] - f[n-1]
       - For interior points (0 < i < n): uses central difference grad[i] = (f[i+1] - f[i-1]) / 2
    3. The gradient has the same size as the input array
    4. The gradient approximates the derivative at each point
    
    This specification assumes unit spacing between points. The actual numpy 
    function can handle custom spacing, but we focus on the core mathematical behavior.
    
    Mathematical properties:
    - For linear functions f(x) = ax + b, the gradient is constant and equal to a
    - For constant functions, the gradient is 0 everywhere
    - The gradient operation is linear: grad(f + g) = grad(f) + grad(g)
    
    Precondition: True (non-empty constraint is in the type Vector Float (n + 1))
    Postcondition: The gradient is computed using appropriate finite difference formulas
-/
theorem numpy_gradient_spec {n : Nat} (f : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_gradient f
    ⦃⇓grad => ⌜-- Core mathematical properties
              -- Single point case: gradient is 0
              (n = 0 → grad.get 0 = 0) ∧ 
              -- Multi-point case: boundary and interior conditions
              (n > 0 → 
                -- First boundary: forward difference
                grad.get 0 = f.get 1 - f.get 0 ∧
                -- Last boundary: backward difference  
                grad.get ⟨n, Nat.lt_succ_self n⟩ = f.get ⟨n, Nat.lt_succ_self n⟩ - f.get ⟨n-1, Nat.pred_lt (ne_of_gt (Nat.zero_lt_succ n))⟩ ∧
                -- Interior points: central difference
                (∀ i : Fin (n + 1), 0 < i.val ∧ i.val < n → 
                  grad.get i = 
                  (f.get ⟨i.val + 1, Nat.succ_lt_succ (And.right ‹0 < i.val ∧ i.val < n›)⟩ - 
                   f.get ⟨i.val - 1, by
                    have h1 : i.val - 1 < n + 1 := by
                      have h2 : i.val ≤ n := Nat.le_of_lt (And.right ‹0 < i.val ∧ i.val < n›)
                      omega
                    exact h1⟩) / 2)) ∧
              -- Additional mathematical properties
              -- For constant functions, gradient is zero everywhere
              (∀ c : Float, (∀ i : Fin (n + 1), f.get i = c) → 
                (∀ i : Fin (n + 1), grad.get i = 0))⌝⦄ := by
  apply spec_of_pre_post
  intro _
  simp
  constructor
  · intro h
    rw [h]
    exact single_point_gradient_zero f
  · constructor
    · intro h
      constructor
      · exact multi_point_first_boundary h f
      · constructor
        · exact multi_point_last_boundary h f
        · exact multi_point_interior h f
    · exact constant_function_gradient_zero f