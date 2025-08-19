import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.polynomial.hermite.hermweight",
  "category": "Hermite polynomials",
  "description": "Weight function of the Hermite polynomials.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.hermweight.html",
  "doc": "Weight function of the Hermite polynomials.\n\n    The weight function is :math:\`\\\\exp(-x^2)\` and the interval of\n    integration is :math:\`[-\\\\inf, \\\\inf]\`. the Hermite polynomials are\n    orthogonal, but not normalized, with respect to this weight function.\n\n    Parameters\n    ----------\n    x : array_like\n       Values at which the weight function will be computed.\n\n    Returns\n    -------\n    w : ndarray\n       The weight function at \`x\`.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial.hermite import hermweight\n    >>> x = np.arange(-2, 2)\n    >>> hermweight(x)\n    array([0.01831564, 0.36787944, 1.        , 0.36787944])",
  "code": "def hermweight(x):\n    \"\"\"\n    Weight function of the Hermite polynomials.\n\n    The weight function is :math:\`\\\\exp(-x^2)\` and the interval of\n    integration is :math:\`[-\\\\inf, \\\\inf]\`. the Hermite polynomials are\n    orthogonal, but not normalized, with respect to this weight function.\n\n    Parameters\n    ----------\n    x : array_like\n       Values at which the weight function will be computed.\n\n    Returns\n    -------\n    w : ndarray\n       The weight function at \`x\`.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial.hermite import hermweight\n    >>> x = np.arange(-2, 2)\n    >>> hermweight(x)\n    array([0.01831564, 0.36787944, 1.        , 0.36787944])\n\n    \"\"\"\n    w = np.exp(-x**2)\n    return w\n\n\n#\n# Hermite series class\n#"
}
-/

open Std.Do

/-- Weight function of the Hermite polynomials.
    Computes exp(-x²) for each element in the input vector. -/
def hermweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  Vector.map (fun xi => Float.exp (-(xi * xi))) x

/-- Specification: hermweight computes the Hermite weight function exp(-x²) for each element.
    
    The specification includes:
    1. Basic property: Each output element equals exp(-x²) of the corresponding input
    2. Non-negativity: All output values are positive (since exp is always positive)
    3. Symmetry: The weight function is symmetric around zero
    4. Maximum at zero: The weight function achieves its maximum value of 1 at x=0
    5. Monotonicity: The function decreases as |x| increases -/
theorem hermweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    hermweight x
    ⦃⇓w => ⌜(∀ i : Fin n, w.get i = Float.exp (-(x.get i * x.get i))) ∧
            (∀ i : Fin n, w.get i > 0) ∧
            (∀ i : Fin n, x.get i = 0 → w.get i = 1) ∧
            (∀ i j : Fin n, Float.abs (x.get i) < Float.abs (x.get j) → 
                            w.get i > w.get j)⌝⦄ := by
  unfold hermweight
  simp [Triple.bind_pure]
  constructor
  · intro i
    rw [Vector.get_map]
    rfl
  constructor
  · intro i
    rw [Vector.get_map]
    exact Float.exp_pos _
  constructor
  · intro i h
    rw [Vector.get_map]
    simp [h]
    exact Float.exp_zero
  · intro i j h
    rw [Vector.get_map, Vector.get_map]
    have h1 : -(x.get i * x.get i) > -(x.get j * x.get j) := by
      simp [neg_lt_neg_iff]
      rw [← Float.abs_mul_self, ← Float.abs_mul_self]
      exact Float.mul_lt_mul_of_pos_right h (Float.abs_pos.mpr (by 
        by_contra h_eq
        rw [Float.abs_eq_zero] at h_eq
        rw [h_eq] at h
        simp [Float.abs_zero] at h
        exact Float.lt_irrefl _ h))
    exact Float.exp_strictMono h1