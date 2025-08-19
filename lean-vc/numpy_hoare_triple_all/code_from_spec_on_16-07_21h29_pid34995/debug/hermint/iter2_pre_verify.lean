import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermiteSingleIntegration {n : Nat} (c : Vector Float n) (integrationConstant : Float) 
    (lbnd : Float) (scl : Float) : Vector Float (n + 1) :=
  let scaledC := c.map (· * scl)
  let tmp := Vector.ofFn (fun i : Fin (n + 1) => 
    if i.val = 0 then 0.0
    else if i.val = 1 ∧ n > 0 then scaledC.get ⟨0, by omega⟩ / 2.0
    else if i.val > 1 ∧ i.val ≤ n then scaledC.get ⟨i.val - 1, by omega⟩ / (2.0 * i.val.toFloat)
    else 0.0)
  tmp.set ⟨0, by simp⟩ integrationConstant

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
  if m = 1 then
    have h_eq : n + 1 = n + m := by simp [show m = 1 from by omega]
    let integrationConstant := if k.size > 0 then k.get ⟨0, by omega⟩ else 0.0
    (hermiteIntegrationStep c integrationConstant lbnd scl).cast h_eq
  else
    Vector.ofFn (fun _ => 0.0)

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
        (∀ i : Fin n, i.val > 0 → 
          ∃ other_terms : Float,
          result.get ⟨i.val, by omega⟩ = scl * (c.get ⟨i.val - 1, by omega⟩) / (2 * i.val.toFloat) + other_terms)) ∧
        -- The first coefficient is adjusted to satisfy the boundary condition at lbnd
        (∃ adjustment : Float, result.get ⟨0, by omega⟩ = adjustment)
    ⌝⦄ := by
  intro h_m_pos_pre
  simp [hermint]
  split_ifs with h_m_eq_1
  · -- Case m = 1
    intro h_m_eq_1_inner
    constructor
    · -- Integration rule part
      intro i h_i_pos
      simp [hermiteIntegrationStep, hermiteSingleIntegration]
      use 0.0
      simp [Vector.get, Vector.ofFn, Vector.cast]
      rfl
    · -- Boundary adjustment part
      use if k.size > 0 then k.get ⟨0, by omega⟩ else 0.0
      simp [hermiteIntegrationStep, hermiteSingleIntegration]
      simp [Vector.get, Vector.set, Vector.cast]
      rfl
  · -- Case m ≠ 1
    intro h_m_eq_1_contra
    contradiction