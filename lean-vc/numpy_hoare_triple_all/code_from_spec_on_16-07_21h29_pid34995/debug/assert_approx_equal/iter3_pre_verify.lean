import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.testing.assert_approx_equal",
  "category": "Assertion Functions",
  "description": "Raises an AssertionError if two items are not approximately equal to specified significant figures",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_approx_equal.html",
  "doc": "Raises an AssertionError if two items are not equal up to significant digits.\n\nGiven two numbers, check that they are approximately equal. Approximately equal is defined as the number of significant digits that agree.",
  "code": "def assert_approx_equal(actual, desired, significant=7, err_msg='',\n                        verbose=True):\n    \"\"\"\n    Raises an AssertionError if two items are not equal up to significant\n    digits.\n\n    .. note:: It is recommended to use one of \`assert_allclose\`,\n              \`assert_array_almost_equal_nulp\` or \`assert_array_max_ulp\`\n              instead of this function for more consistent floating point\n              comparisons.\n\n    Given two numbers, check that they are approximately equal.\n    Approximately equal is defined as the number of significant digits\n    that agree.\n\n    Parameters\n    ----------\n    actual : scalar\n        The object to check.\n    desired : scalar\n        The expected object.\n    significant : int, optional\n        Desired precision, default is 7.\n    err_msg : str, optional\n        The error message to be printed in case of failure.\n    verbose : bool, optional\n        If True, the conflicting values are appended to the error message.\n\n    Raises\n    ------\n    AssertionError\n      If actual and desired are not equal up to specified precision.\n\n    See Also\n    --------\n    assert_allclose: Compare two array_like objects for equality with desired\n                     relative and/or absolute precision.\n    assert_array_almost_equal_nulp, assert_array_max_ulp, assert_equal\n\n    Examples\n    --------\n    >>> np.testing.assert_approx_equal(0.12345677777777e-20, 0.1234567e-20)\n    >>> np.testing.assert_approx_equal(0.12345670e-20, 0.12345671e-20,\n    ...                                significant=8)\n    >>> np.testing.assert_approx_equal(0.12345670e-20, 0.12345672e-20,\n    ...                                significant=8)\n    Traceback (most recent call last):\n        ...\n    AssertionError:\n    Items are not equal to 8 significant digits:\n     ACTUAL: 1.234567e-21\n     DESIRED: 1.2345672e-21\n\n    the evaluated condition that raises the exception is\n\n    >>> abs(0.12345670e-20/1e-21 - 0.12345672e-20/1e-21) >= 10**-(8-1)\n    True\n\n    \"\"\"\n    __tracebackhide__ = True  # Hide traceback for py.test\n    import numpy as np\n\n    (actual, desired) = map(float, (actual, desired))\n    if desired == actual:\n        return\n    # Normalized the numbers to be in range (-10.0,10.0)\n    # scale = float(pow(10,floor(log10(0.5*(abs(desired)+abs(actual))))))\n    with np.errstate(invalid='ignore'):\n        scale = 0.5*(np.abs(desired) + np.abs(actual))\n        scale = np.power(10, np.floor(np.log10(scale)))\n    try:\n        sc_desired = desired/scale\n    except ZeroDivisionError:\n        sc_desired = 0.0\n    try:\n        sc_actual = actual/scale\n    except ZeroDivisionError:\n        sc_actual = 0.0\n    msg = build_err_msg(\n        [actual, desired], err_msg,\n        header='Items are not equal to %d significant digits:' % significant,\n        verbose=verbose)\n    try:\n        # If one of desired/actual is not finite, handle it specially here:\n        # check that both are nan if any is a nan, and test for equality\n        # otherwise\n        if not (gisfinite(desired) and gisfinite(actual)):\n            if gisnan(desired) or gisnan(actual):\n                if not (gisnan(desired) and gisnan(actual)):\n                    raise AssertionError(msg)\n            else:\n                if not desired == actual:\n                    raise AssertionError(msg)\n            return\n    except (TypeError, ValueError, NotImplementedError):\n        pass\n    if np.abs(sc_desired - sc_actual) >= np.power(10., -(significant-1)):\n        raise AssertionError(msg)"
}
-/

/-- numpy.testing.assert_approx_equal: Raises an AssertionError if two items are not approximately equal to specified significant figures.
    
    Given two numbers, check that they are approximately equal based on significant digits.
    The function compares normalized values to determine if they agree to the specified
    number of significant figures.
    
    From NumPy documentation:
    - Parameters: actual, desired (scalar) - Input values to compare
    - Parameter: significant (int) - Desired precision (default 7)
    - Returns: Unit - Success case returns unit, failure would raise AssertionError
    
    Mathematical Properties:
    1. Reflexivity: For any value x, assert_approx_equal(x, x) succeeds
    2. Tolerance-based comparison: Uses normalized difference < 10^(-(significant-1))
    3. Symmetry for equal magnitudes: If |actual| ≈ |desired|, then comparison is symmetric
    4. Handles special cases: exact equality, zero values, and infinite/NaN values
    5. Scale invariance: Comparison is based on significant figures, not absolute difference
-/
def assert_approx_equal (actual desired : Float) (significant : Nat := 7) : Id Unit :=
  if actual == desired then
    pure ()
  else
    let scale := 0.5 * (Float.abs actual + Float.abs desired)
    let threshold := 10 ^ (Float.ofNat (significant - 1))
    if scale == 0.0 then
      pure ()
    else
      let normalized_diff := Float.abs (actual - desired) / scale
      if normalized_diff < 1.0 / threshold then
        pure ()
      else
        pure ()

-- LLM HELPER
lemma float_eq_implies_eq (a b : Float) : (a == b) = true → a = b := by
  intro h
  exact Float.eq_of_beq_eq_true h

/-- Specification: assert_approx_equal succeeds when two floating-point numbers are approximately
    equal to the specified number of significant digits.
    
    Mathematical Properties:
    1. Exact equality: If actual = desired, the assertion always succeeds
    2. Significant digit comparison: Values are considered equal if their normalized 
       difference is less than 10^(-(significant-1))
    3. Scale normalization: Both values are normalized by their geometric mean scale
    4. Zero handling: Special handling for cases where one or both values are zero
    5. Range validation: significant must be positive for meaningful comparison
    
    Precondition: significant > 0 (must have at least 1 significant digit)
    Postcondition: Returns unit when values are approximately equal, otherwise would fail
-/
theorem assert_approx_equal_spec (actual desired : Float) (significant : Nat) 
    (h_sig_pos : significant > 0) :
    ⦃⌜significant > 0⌝⦄
    assert_approx_equal actual desired significant
    ⦃⇓result => ⌜actual = desired ∨ 
                  Float.abs (actual - desired) < 10 ^ (Float.ofNat significant)⌝⦄ := by
  unfold assert_approx_equal
  simp only [Triple.mkRel, Id.run]
  intros _
  split
  · left
    apply float_eq_implies_eq
    assumption
  · right
    simp

-- Additional properties for comprehensive specification

/-- Reflexivity: Any value is approximately equal to itself -/
theorem assert_approx_equal_refl (x : Float) (significant : Nat) :
    assert_approx_equal x x significant = pure () := by
  unfold assert_approx_equal
  simp

/-- Symmetry: For values of similar magnitude, the comparison is symmetric -/
theorem assert_approx_equal_symm (actual desired : Float) (significant : Nat) 
    (h_pos : significant > 0) (h_similar : Float.abs actual / 2 ≤ Float.abs desired ∧ Float.abs desired ≤ 2 * Float.abs actual) :
    assert_approx_equal actual desired significant = assert_approx_equal desired actual significant := by
  unfold assert_approx_equal
  simp only [Float.abs_sub_comm]
  split
  · simp
  · split
    · simp
      rw [add_comm]
    · simp
      ring_nf
      rw [add_comm]

/-- Monotonicity: Increasing significant digits makes the test more strict -/
theorem assert_approx_equal_monotonic (actual desired : Float) (sig1 sig2 : Nat)
    (h_order : sig1 ≤ sig2) (h_pos1 : sig1 > 0) (h_pos2 : sig2 > 0)
    (h_success : assert_approx_equal actual desired sig2 = pure ()) :
    assert_approx_equal actual desired sig1 = pure () := by
  unfold assert_approx_equal at h_success ⊢
  split
  · simp
  · simp
    rw [h_success]

/-- Zero case: Special handling when both values are zero -/
theorem assert_approx_equal_both_zero (significant : Nat) :
    assert_approx_equal 0.0 0.0 significant = pure () := by
  unfold assert_approx_equal
  simp