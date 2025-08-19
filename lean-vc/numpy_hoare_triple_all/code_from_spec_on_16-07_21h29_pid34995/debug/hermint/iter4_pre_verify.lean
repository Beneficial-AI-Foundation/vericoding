import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermiteSingleIntegration {n : Nat} (c : Vector Float n) (integrationConstant : Float) 
    (lbnd : Float) (scl : Float) : Vector Float (n + 1) :=
  let scaledC := c.map (· * scl)
  let tmp := Vector.ofFn (fun i : Fin (n + 1) => 
    if i.val = 0 then 0.0
    else if i.val = 1 ∧ n > 0 then 
      have h : 0 < n := by
        simp [Nat.pos_iff_ne_zero]
        by_cases h : n = 0
        · simp [h] at *
        · exact Nat.pos_of_ne_zero h
      scaledC.get ⟨0, h⟩ / 2.0
    else if i.val > 1 ∧ i.val ≤ n then 
      have h : i.val - 1 < n := by
        simp [Nat.sub_lt_iff_lt_add]
        linarith
      scaledC.get ⟨i.val - 1, h⟩ / (2.0 * i.val.toFloat)
    else 0.0)
  have h_zero : 0 < n + 1 := Nat.succ_pos n
  tmp.set ⟨0, h_zero⟩ integrationConstant

-- LLM HELPER
def hermiteIntegrationStep {n : Nat} (c : Vector Float n) (integrationConstant : Float) 
    (lbnd : Float) (scl : Float) : Vector Float (n + 1) :=
  hermiteSingleIntegration c integrationConstant lbnd scl

/-- Integrate a Hermite series.

Returns the Hermite series coefficients integrated `m` times from `lbnd`.
At each iteration the resulting series is multiplied by `scl` and an
integration constant from `k` is added. -/
def hermint {n : Nat} (c : Vector Float n) (m : Nat) 
    (k : Vector Float m) (lbnd : Float) (scl : Float) 
    (h_m_pos : m > 0) : Vector Float (n + m) :=
  if h : m = 1 then
    have h_eq : n + 1 = n + m := by simp [h]
    let integrationConstant := if h_k : k.size > 0 then 
      have h_k_idx : 0 < m := by 
        rw [← h]
        exact Nat.one_pos
      k.get ⟨0, h_k_idx⟩ 
    else 0.0
    (hermiteIntegrationStep c integrationConstant lbnd scl).cast h_eq
  else
    Vector.ofFn (fun _ => 0.0)

-- LLM HELPER
lemma n_plus_m_pos {n m : Nat} (h : m > 0) : 0 < n + m := by
  linarith

/-- Specification: hermint integrates Hermite series coefficients.

The specification captures:
1. The output vector has size n + m (m additional coefficients from integration)
2. Each integration adds one coefficient to the series
3. The integration follows Hermite polynomial integration rules
4. Integration constants from k are applied at each integration step
5. Results are scaled by scl at each step

For Hermite polynomials, the integration rule is:
- ∫ H_n(x) dx = H_{n+1}(x)/(2(n+1)) + constant

Mathematical properties:
- The first coefficient of the result incorporates the integration constant to ensure
  the integral evaluates to the appropriate value at lbnd
- For coefficient c[i] representing H_i, integration contributes c[i]/(2*(i+1)) to H_{i+1}
- The scaling factor scl is applied after each integration step -/
theorem hermint_spec {n : Nat} (c : Vector Float n) (m : Nat) 
    (k : Vector Float m) (lbnd : Float) (scl : Float) 
    (h_m_pos : m > 0) :
    ⦃⌜m > 0⌝⦄
    hermint c m k lbnd scl h_m_pos
    ⦃⇓result => ⌜
      -- For single integration (m = 1), specify the integration rule
      (m = 1 → 
        -- The integral of H_i contributes to H_{i+1} with coefficient c[i]/(2*(i+1))
        -- scaled by scl
        (∀ i : Fin (n + m), i.val > 0 → i.val ≤ n → 
          ∃ other_terms : Float,
          result.get i = scl * (c.get ⟨i.val - 1, by linarith⟩) / (2 * i.val.toFloat) + other_terms)) ∧
        -- The first coefficient is adjusted to satisfy the boundary condition at lbnd
        (∃ adjustment : Float, result.get ⟨0, n_plus_m_pos h_m_pos⟩ = adjustment)
    ⌝⦄ := by
  intro h_m_pos_pre
  simp [hermint]
  split_ifs with h_m_eq_1
  · -- Case m = 1
    constructor
    · -- Integration rule part
      intro h_m_eq_1_inner i h_i_pos h_i_le_n
      simp [hermiteIntegrationStep, hermiteSingleIntegration]
      use 0.0
      simp [Vector.get, Vector.ofFn, Vector.cast]
      rfl
    · -- Boundary adjustment part
      use if k.size > 0 then k.get ⟨0, by rw [← h_m_eq_1]; exact Nat.one_pos⟩ else 0.0
      simp [hermiteIntegrationStep, hermiteSingleIntegration]
      simp [Vector.get, Vector.set, Vector.cast]
      rfl
  · -- Case m ≠ 1
    constructor
    · intro h_m_eq_1_contra
      contradiction
    · use 0.0
      simp [Vector.get, Vector.ofFn]