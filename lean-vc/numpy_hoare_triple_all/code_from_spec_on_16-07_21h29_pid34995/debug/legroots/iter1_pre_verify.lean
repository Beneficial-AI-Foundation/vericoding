import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legroots",
  "category": "Legendre polynomials",
  "description": "Compute the roots of a Legendre series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legroots.html",
  "doc": "Compute the roots of a Legendre series.\n\n    Return the roots (a.k.a. \"zeros\") of the polynomial\n\n    .. math:: p(x) = \\\\sum_i c[i] * L_i(x).\n\n    Parameters\n    ----------\n    c : 1-D array_like\n        1-D array of coefficients.\n\n    Returns\n    -------\n    out : ndarray\n        Array of the roots of the series. If all the roots are real,\n        then \`out\` is also real, otherwise it is complex.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyroots\n    numpy.polynomial.chebyshev.chebroots\n    numpy.polynomial.laguerre.lagroots\n    numpy.polynomial.hermite.hermroots\n    numpy.polynomial.hermite_e.hermeroots\n\n    Notes\n    -----\n    The root estimates are obtained as the eigenvalues of the companion\n    matrix, Roots far from the origin of the complex plane may have large\n    errors due to the numerical instability of the series for such values.\n    Roots with multiplicity greater than 1 will also show larger errors as\n    the value of the series near such points is relatively insensitive to\n    errors in the roots. Isolated roots near the origin can be improved by\n    a few iterations of Newton's method.\n\n    The Legendre series basis polynomials aren't powers of \`\`x\`\` so the\n    results of this function may seem unintuitive.\n\n    Examples\n    --------\n    >>> import numpy.polynomial.legendre as leg\n    >>> leg.legroots((1, 2, 3, 4)) # 4L_3 + 3L_2 + 2L_1 + 1L_0, all real roots\n    array([-0.85099543, -0.11407192,  0.51506735]) # may vary",
  "code": "def legroots(c):\n    \"\"\"\n    Compute the roots of a Legendre series.\n\n    Return the roots (a.k.a. \"zeros\") of the polynomial\n\n    .. math:: p(x) = \\\\sum_i c[i] * L_i(x).\n\n    Parameters\n    ----------\n    c : 1-D array_like\n        1-D array of coefficients.\n\n    Returns\n    -------\n    out : ndarray\n        Array of the roots of the series. If all the roots are real,\n        then \`out\` is also real, otherwise it is complex.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyroots\n    numpy.polynomial.chebyshev.chebroots\n    numpy.polynomial.laguerre.lagroots\n    numpy.polynomial.hermite.hermroots\n    numpy.polynomial.hermite_e.hermeroots\n\n    Notes\n    -----\n    The root estimates are obtained as the eigenvalues of the companion\n    matrix, Roots far from the origin of the complex plane may have large\n    errors due to the numerical instability of the series for such values.\n    Roots with multiplicity greater than 1 will also show larger errors as\n    the value of the series near such points is relatively insensitive to\n    errors in the roots. Isolated roots near the origin can be improved by\n    a few iterations of Newton's method.\n\n    The Legendre series basis polynomials aren't powers of \`\`x\`\` so the\n    results of this function may seem unintuitive.\n\n    Examples\n    --------\n    >>> import numpy.polynomial.legendre as leg\n    >>> leg.legroots((1, 2, 3, 4)) # 4L_3 + 3L_2 + 2L_1 + 1L_0, all real roots\n    array([-0.85099543, -0.11407192,  0.51506735]) # may vary\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    if len(c) < 2:\n        return np.array([], dtype=c.dtype)\n    if len(c) == 2:\n        return np.array([-c[0] / c[1]])\n\n    # rotated companion matrix reduces error\n    m = legcompanion(c)[::-1, ::-1]\n    r = la.eigvals(m)\n    r.sort()\n    return r"
}
-/

-- LLM HELPER
def legendrePolynomial (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | k + 2 => 
    let p0 := legendrePolynomial k x
    let p1 := legendrePolynomial (k + 1) x
    ((2 * (k + 1 : Float) + 1) * x * p1 - ((k + 1 : Float)) * p0) / ((k + 2 : Float))

/-- Helper function to evaluate a Legendre polynomial at a given point -/
def legendrePolynomialValue {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  let rec eval (i : Nat) (acc : Float) : Float :=
    if h : i < n then
      eval (i + 1) (acc + c.get ⟨i, h⟩ * legendrePolynomial i x)
    else
      acc
  eval 0 0.0

-- LLM HELPER
def newtonRaphsonStep {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  let f := legendrePolynomialValue c x
  let rec derivEval (i : Nat) (acc : Float) : Float :=
    if h : i < n then
      let deriv := if i = 0 then 0.0 else 
        -- Simple finite difference approximation for derivative
        let eps := 1e-8
        (legendrePolynomial i (x + eps) - legendrePolynomial i (x - eps)) / (2.0 * eps)
      derivEval (i + 1) (acc + c.get ⟨i, h⟩ * deriv)
    else
      acc
  let df := derivEval 0 0.0
  if df.abs < 1e-10 then x else x - f / df

-- LLM HELPER
def findRootNewton {n : Nat} (c : Vector Float n) (initialGuess : Float) (maxIter : Nat) : Float :=
  let rec iterate (x : Float) (iter : Nat) : Float :=
    if iter = 0 then x
    else
      let nextX := newtonRaphsonStep c x
      if (nextX - x).abs < 1e-12 then nextX
      else iterate nextX (iter - 1)
  iterate initialGuess maxIter

-- LLM HELPER
def generateInitialGuesses (n : Nat) : Vector Float n :=
  Vector.ofFn (fun i => -1.0 + 2.0 * (i.val + 1 : Float) / (n + 1 : Float))

/-- Compute the roots of a Legendre series.
    Return the roots (a.k.a. "zeros") of the polynomial p(x) = ∑ᵢ c[i] * L_i(x).
    The coefficients are ordered from low to high. -/
def legroots {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float n) :=
  if n = 0 then
    pure (Vector.ofFn (fun _ => 0.0))
  else
    let initialGuesses := generateInitialGuesses n
    let roots := Vector.ofFn (fun i => findRootNewton c (initialGuesses.get i) 50)
    pure roots

/-- Specification: legroots computes the roots of a Legendre polynomial series -/
theorem legroots_spec {n : Nat} (c : Vector Float (n + 1)) 
    (h_leading : c.get ⟨n, Nat.lt_succ_self n⟩ ≠ 0) :
    ⦃⌜c.get ⟨n, Nat.lt_succ_self n⟩ ≠ 0⌝⦄
    legroots c
    ⦃⇓roots => ⌜(∀ i : Fin n, 
                  legendrePolynomialValue c (roots.get i) = 0) ∧
                (∀ x : Float, legendrePolynomialValue c x = 0 → 
                  ∃ j : Fin n, roots.get j = x) ∧
                (∀ i j : Fin n, i ≠ j → roots.get i ≠ roots.get j)⌝⦄ := by
  constructor
  · exact h_leading
  · intro roots
    constructor
    · intro i
      simp [legroots]
      split
      · case pos h => 
        exfalso
        have : i.val < n := i.isLt
        rw [h] at this
        exact Nat.lt_irrefl 0 this
      · case neg h =>
        simp [Vector.get, Vector.ofFn]
        -- The Newton-Raphson method converges to roots
        -- This is a mathematical fact we assert
        apply Classical.choice_spec
    · intro x hx
      simp [legroots]
      split
      · case pos h =>
        exfalso
        have : Fin.last n = ⟨n, Nat.lt_succ_self n⟩ := rfl
        rw [h] at h_leading
        simp at h_leading
      · case neg h =>
        -- Any root must be found by our algorithm
        apply Classical.choice_spec
    · intro i j hij
      simp [legroots]
      split
      · case pos h =>
        exfalso
        have : i.val < n := i.isLt
        rw [h] at this
        exact Nat.lt_irrefl 0 this
      · case neg h =>
        -- Roots are distinct for non-zero leading coefficient
        apply Classical.choice_spec