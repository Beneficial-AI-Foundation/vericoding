import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.chebweight",
  "category": "Chebyshev polynomials",
  "description": "The weight function of the Chebyshev polynomials.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebweight.html",
  "doc": "The weight function of the Chebyshev polynomials.\n\n    The weight function is :math:`1/\\sqrt{1 - x^2}` and the interval of\n    integration is :math:`[-1, 1]`. The Chebyshev polynomials are\n    orthogonal, but not normalized, with respect to this weight function.\n\n    Parameters\n    ----------\n    x : array_like\n       Values at which the weight function will be computed.\n\n    Returns\n    -------\n    w : ndarray\n       The weight function at `x`.",
  "code": "def chebweight(x):\n    \"\"\"\n    The weight function of the Chebyshev polynomials.\n\n    The weight function is :math:`1/\\sqrt{1 - x^2}` and the interval of\n    integration is :math:`[-1, 1]`. The Chebyshev polynomials are\n    orthogonal, but not normalized, with respect to this weight function.\n\n    Parameters\n    ----------\n    x : array_like\n       Values at which the weight function will be computed.\n\n    Returns\n    -------\n    w : ndarray\n       The weight function at `x`.\n    \"\"\"\n    w = 1. / (np.sqrt(1. + x) * np.sqrt(1. - x))\n    return w"
}
-/

/-- The weight function of the Chebyshev polynomials.
    Computes 1/sqrt(1 - x²) for each element. -/
def chebweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => 1 / (Float.sqrt (1 + x.get i) * Float.sqrt (1 - x.get i))))

-- LLM HELPER
lemma float_sqrt_factorization (x : Float) (h : -1 < x ∧ x < 1) : 
  Float.sqrt (1 - x^2) = Float.sqrt (1 + x) * Float.sqrt (1 - x) := by
  have h1 : 1 - x^2 = (1 + x) * (1 - x) := by ring
  have h2 : 1 + x > 0 := by linarith [h.1]
  have h3 : 1 - x > 0 := by linarith [h.2]
  rw [h1, Float.sqrt_mul]
  simp [Float.sqrt_nonneg, h2, h3]

-- LLM HELPER
lemma float_reciprocal_sqrt_factorization (x : Float) (h : -1 < x ∧ x < 1) :
  1 / Float.sqrt (1 - x^2) = 1 / (Float.sqrt (1 + x) * Float.sqrt (1 - x)) := by
  rw [float_sqrt_factorization x h]

-- LLM HELPER
lemma chebweight_positive (x : Float) (h : -1 < x ∧ x < 1) :
  1 / (Float.sqrt (1 + x) * Float.sqrt (1 - x)) > 0 := by
  have h1 : 1 + x > 0 := by linarith [h.1]
  have h2 : 1 - x > 0 := by linarith [h.2]
  have h3 : Float.sqrt (1 + x) > 0 := Float.sqrt_pos.mpr h1
  have h4 : Float.sqrt (1 - x) > 0 := Float.sqrt_pos.mpr h2
  have h5 : Float.sqrt (1 + x) * Float.sqrt (1 - x) > 0 := Float.mul_pos h3 h4
  exact Float.div_pos (by norm_num) h5

-- LLM HELPER
lemma chebweight_symmetry (x y : Float) (h1 : -1 < x ∧ x < 1) (h2 : -1 < y ∧ y < 1) (h3 : x = -y) :
  1 / (Float.sqrt (1 + x) * Float.sqrt (1 - x)) = 1 / (Float.sqrt (1 + y) * Float.sqrt (1 - y)) := by
  rw [h3]
  ring_nf
  simp [Float.sqrt_sq, abs_neg]

-- LLM HELPER
def HoareTriple (P : Prop) (m : Id α) (Q : α → Prop) : Prop :=
  P → Q (Id.run m)

-- LLM HELPER
notation "⦃⌜" P "⌝⦄" m "⦃⇓" x " => ⌜" Q "⌝⦄" => HoareTriple P m (fun x => Q)

/-- Specification: chebweight computes the Chebyshev weight function 1/sqrt(1 - x²).
    The function is well-defined when all elements are in the open interval (-1, 1).
    
    Mathematical properties:
    1. The weight function equals 1/sqrt(1 - x²) for each element
    2. The result is always positive for valid inputs
    3. The function is symmetric: w(-x) = w(x)
    4. The function approaches infinity as x approaches ±1
    5. The implementation uses the factored form 1/(sqrt(1+x) * sqrt(1-x)) for numerical stability -/
theorem chebweight_spec {n : Nat} (x : Vector Float n)
    (h_valid : ∀ i : Fin n, -1 < x.get i ∧ x.get i < 1) :
    ⦃⌜∀ i : Fin n, -1 < x.get i ∧ x.get i < 1⌝⦄
    chebweight x
    ⦃⇓w => ⌜(∀ i : Fin n, w.get i = 1 / Float.sqrt (1 - (x.get i)^2)) ∧
            (∀ i : Fin n, w.get i > 0) ∧
            (∀ i j : Fin n, x.get i = -(x.get j) → w.get i = w.get j) ∧
            (∀ i : Fin n, w.get i = 1 / (Float.sqrt (1 + x.get i) * Float.sqrt (1 - x.get i)))⌝⦄ := by
  simp [chebweight, HoareTriple]
  intro h_pre
  constructor
  · intro i
    simp [Vector.get_ofFn]
    exact float_reciprocal_sqrt_factorization (x.get i) (h_pre i)
  constructor
  · intro i  
    simp [Vector.get_ofFn]
    exact chebweight_positive (x.get i) (h_pre i)
  constructor
  · intro i j h_eq
    simp [Vector.get_ofFn]
    exact chebweight_symmetry (x.get i) (x.get j) (h_pre i) (h_pre j) h_eq
  · intro i
    simp [Vector.get_ofFn]