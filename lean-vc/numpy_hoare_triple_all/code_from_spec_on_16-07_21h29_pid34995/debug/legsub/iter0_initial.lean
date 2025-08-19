import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legsub",
  "category": "Legendre polynomials",
  "description": "Subtract one Legendre series from another.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legsub.html",
  "doc": "Subtract one Legendre series from another.\n\n    Returns the difference of two Legendre series \`c1\` - \`c2\`.  The\n    sequences of coefficients are from lowest order term to highest, i.e.,\n    [1,2,3] represents the series \`\`P_0 + 2*P_1 + 3*P_2\`\`.\n\n    Parameters\n    ----------\n    c1, c2 : array_like\n        1-D arrays of Legendre series coefficients ordered from low to\n        high.\n\n    Returns\n    -------\n    out : ndarray\n        Of Legendre series coefficients representing their difference.\n\n    See Also\n    --------\n    legadd, legmulx, legmul, legdiv, legpow\n\n    Notes\n    -----\n    Unlike multiplication, division, etc., the difference of two Legendre\n    series is a Legendre series (without having to \"reproject\" the result\n    onto the basis set) so subtraction, just like that of \"standard\"\n    polynomials, is simply \"component-wise.\"\n\n    Examples\n    --------\n    >>> from numpy.polynomial import legendre as L\n    >>> c1 = (1,2,3)\n    >>> c2 = (3,2,1)\n    >>> L.legsub(c1,c2)\n    array([-2.,  0.,  2.])\n    >>> L.legsub(c2,c1) # -C.legsub(c1,c2)\n    array([ 2.,  0., -2.])\n\n    \"\"\"\n    return pu._sub(c1, c2)"
}
-/

-- LLM HELPER
/-- Legendre polynomial of degree n at point x -/
def legendre (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | n + 2 => 
    let rec helper (k : Nat) (p0 p1 : Float) : Float :=
      if k = 0 then p1
      else
        let p2 := ((2 * k.toFloat + 1) * x * p1 - k.toFloat * p0) / (k.toFloat + 1)
        helper (k - 1) p1 p2
    helper n 1.0 x

/-- Helper function to evaluate a Legendre series at a given point -/
def legendreSeriesValue {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  let rec helper (i : Nat) (acc : Float) : Float :=
    if h : i < n then
      let coeff := c.get ⟨i, h⟩
      helper (i + 1) (acc + coeff * legendre i x)
    else acc
  helper 0 0.0

/-- Subtract one Legendre series from another.
    Returns the difference of two Legendre series c1 - c2.
    The sequences of coefficients are from lowest order term to highest,
    i.e., [1,2,3] represents the series P_0 + 2*P_1 + 3*P_2. -/
def legsub {n : Nat} (c1 c2 : Vector Float n) : Id (Vector Float n) :=
  Id.mk (Vector.mk (fun i => c1.get i - c2.get i))

-- LLM HELPER
/-- Linearity of Legendre series evaluation -/
lemma legendreSeriesValue_sub {n : Nat} (c1 c2 : Vector Float n) (x : Float) :
    legendreSeriesValue (Vector.mk (fun i => c1.get i - c2.get i)) x = 
    legendreSeriesValue c1 x - legendreSeriesValue c2 x := by
  unfold legendreSeriesValue
  let rec helper_eq (i : Nat) (acc1 acc2 : Float) : 
      (let rec helper (j : Nat) (acc : Float) : Float :=
         if h : j < n then
           let coeff := (Vector.mk (fun k => c1.get k - c2.get k)).get ⟨j, h⟩
           helper (j + 1) (acc + coeff * legendre j x)
         else acc;
       helper i (acc1 - acc2)) = 
      (let rec helper1 (j : Nat) (acc : Float) : Float :=
         if h : j < n then
           let coeff := c1.get ⟨j, h⟩
           helper1 (j + 1) (acc + coeff * legendre j x)
         else acc;
       helper1 i acc1) -
      (let rec helper2 (j : Nat) (acc : Float) : Float :=
         if h : j < n then
           let coeff := c2.get ⟨j, h⟩
           helper2 (j + 1) (acc + coeff * legendre j x)
         else acc;
       helper2 i acc2) := by
    induction i using Nat.strong_induction_on with
    | ind k ih =>
      simp [Float.sub_add_cancel, Float.add_sub_cancel]
      split <;> simp [Float.sub_add_cancel, Float.add_sub_cancel]
  exact helper_eq 0 0.0 0.0

/-- Specification: legsub performs component-wise subtraction of Legendre series coefficients -/
theorem legsub_spec {n : Nat} (c1 c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    legsub c1 c2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = c1.get i - c2.get i) ∧
                 (∀ x : Float, legendreSeriesValue result x = 
                   legendreSeriesValue c1 x - legendreSeriesValue c2 x)⌝⦄ := by
  unfold legsub
  simp [DSpec.post_ret]
  constructor
  · intro i
    simp [Vector.get_mk]
  · intro x
    simp [Vector.get_mk]
    exact legendreSeriesValue_sub c1 c2 x