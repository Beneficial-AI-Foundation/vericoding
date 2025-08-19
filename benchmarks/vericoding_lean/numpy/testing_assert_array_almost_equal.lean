import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.testing.assert_array_almost_equal",
  "category": "Assertion Functions",
  "description": "Raises an AssertionError if two objects are not equal up to desired precision",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_array_almost_equal.html",
  "doc": "Raises an AssertionError if two objects are not equal up to desired precision.\n\nThe test verifies identical shapes and that the elements of \`\`actual\`\` and \`\`desired\`\` satisfy \`\`abs(desired-actual) < 1.5 * 10**(-decimal)\`\`.\n\nThe equality of NaN values is checked. If the dtype of the arrays is float32, then the threshold for the absolute difference is 1e-5.\n\nException is raised at shape mismatch or conflicting values. In contrast to the standard usage in numpy, NaNs are compared like numbers, no assertion is raised if both objects have NaNs in the same positions.",
  "code": "def assert_array_almost_equal(actual, desired, decimal=6, err_msg='',\n                              verbose=True):\n    \"\"\"\n    Raises an AssertionError if two objects are not equal up to desired\n    precision.\n\n    The test verifies identical shapes and that the elements of \`\`actual\`\`\n    and \`\`desired\`\` satisfy \`\`abs(desired-actual) < 1.5 * 10**(-decimal)\`\`.\n\n    The equality of NaN values is checked.  If the dtype of the arrays is\n    float32, then the threshold for the absolute difference is 1e-5.\n\n    Exception is raised at shape mismatch or conflicting values. In contrast\n    to the standard usage in numpy, NaNs are compared like numbers, no\n    assertion is raised if both objects have NaNs in the same positions.\n\n    Parameters\n    ----------\n    actual : array_like\n        The actual object to check.\n    desired : array_like\n        The desired, expected object.\n    decimal : int, optional\n        Desired precision, default is 6.\n    err_msg : str, optional\n        The error message to be printed in case of failure.\n    verbose : bool, optional\n        If True, the conflicting values are appended to the error message.\n\n    Raises\n    ------\n    AssertionError\n        If actual and desired are not equal up to specified precision.\n\n    See Also\n    --------\n    assert_allclose: Compare two array_like objects for equality with desired\n                     relative and/or absolute precision.\n    assert_array_almost_equal_nulp, assert_array_max_ulp, assert_equal\n\n    Examples\n    --------\n    the first assert does not raise an exception\n\n    >>> np.testing.assert_array_almost_equal([1.0,2.333,np.nan],\n    ...                                      [1.0,2.333,np.nan])\n\n    >>> np.testing.assert_array_almost_equal([1.0,2.33333,np.nan],\n    ...                                      [1.0,2.33339,np.nan], decimal=5)\n    Traceback (most recent call last):\n        ...\n    AssertionError:\n    Arrays are not almost equal to 5 decimals\n    <BLANKLINE>\n    Mismatched elements: 1 / 3 (33.3%)\n    Max absolute difference among violations: 6.e-05\n    Max relative difference among violations: 2.57136612e-05\n     ACTUAL: array([1.     , 2.33333,     nan])\n     DESIRED: array([1.     , 2.33339,     nan])\n\n    >>> np.testing.assert_array_almost_equal([1.0,2.33333,np.nan],\n    ...                                      [1.0,2.33333, 5], decimal=5)\n    Traceback (most recent call last):\n        ...\n    AssertionError:\n    Arrays are not almost equal to 5 decimals\n    <BLANKLINE>\n    NaN location mismatch:\n     ACTUAL: array([1.     , 2.33333,     nan])\n     DESIRED: array([1.     , 2.33333, 5.     ])\n\n    \"\"\"\n    __tracebackhide__ = True  # Hide traceback for py.test\n    from numpy import number, float_, result_type\n    def compare(x, y):\n        try:\n            if np.issubdtype(x.dtype, number) and np.issubdtype(y.dtype, number):\n                if hasattr(y, 'dtype'):\n                    dtype = result_type(x, y)\n                else:\n                    dtype = x.dtype\n                if np.issubdtype(dtype, float_):\n                    dtype = np.dtype(float_)\n                x_isnan, y_isnan = isnan(x), isnan(y)\n                x_isinf, y_isinf = isinf(x), isinf(y)\n                \n                # Remove NaN (and inf) unless both are NaN (or inf) at the same\n                # locations.\n                x_id_nan_inf = x_isnan | x_isinf\n                y_id_nan_inf = y_isnan | y_isinf\n                # Only do the removal if NaN (or inf) is present (expensive for\n                # large arrays).\n                if np.any(x_id_nan_inf) or np.any(y_id_nan_inf):\n                    # NaN and inf are considered \"equal\"\n                    if not (x_id_nan_inf == y_id_nan_inf).all():\n                        return False\n                    val = np.empty_like(x, dtype=dtype).flat\n                    val[:] = [0 if x_id_nan_inf[i]\n                              else x[i] for i in ndindex(x.shape)]\n                    x = val\n                    val = np.empty_like(y, dtype=dtype).flat\n                    val[:] = [0 if y_id_nan_inf[i]\n                              else y[i] for i in ndindex(y.shape)]\n                    y = val\n            # Check that inexact dtypes are not mixed with exact dtypes\n            elif (np.issubdtype(x.dtype, np.inexact) != \n                  np.issubdtype(y.dtype, np.inexact)):\n                return False\n        except (ValueError, TypeError):\n            return False\n        # Divide by 2 to avoid overflow issues with uint8\n        if decimal >= 1:\n            if np.issubdtype(y.dtype, np.integer):\n                return (np.abs(x.astype(float_) - y.astype(float_)) <\n                        0.5 * 10.0**(-decimal)).all()\n            else:\n                return (np.abs(x - y) < 1.5 * 10.0**(-decimal)).all()\n        else:\n            return (np.abs(x - y) < 10.0**(-decimal)).all()\n    assert_array_compare(compare, actual, desired, err_msg=err_msg,\n                         verbose=verbose,\n                         header=('Arrays are not almost equal to %d decimals' %\n                                 decimal), precision=decimal)"
}
-/

open Std.Do

/-- Check if two vectors are almost equal up to desired precision.
    Returns true if the assertion passes, false if it would raise an AssertionError. -/
def assert_array_almost_equal {n : Nat} (actual desired : Vector Float n) (decimal : Nat := 6) : Id Bool :=
  sorry

/-- Specification: assert_array_almost_equal checks if two arrays are almost equal up to desired precision.
    The function verifies that abs(desired[i] - actual[i]) < tolerance for all elements.
    Mathematical properties:
    1. Symmetry: almost_equal(a, b) = almost_equal(b, a)
    2. Reflexivity: almost_equal(a, a) = True
    3. Tolerance bound: abs(desired[i] - actual[i]) < tolerance for success
    4. Precision scaling: smaller decimal means looser tolerance
    5. Element-wise comparison: all elements must satisfy the tolerance individually -/
theorem assert_array_almost_equal_spec {n : Nat} (actual desired : Vector Float n) (decimal : Nat) :
    ⦃⌜True⌝⦄
    assert_array_almost_equal actual desired decimal
    ⦃⇓result => ⌜result = true ↔ 
                  (let tolerance := if decimal ≥ 1 then 1.5 * (10 : Float) ^ (-(decimal : Nat).toFloat) else (10 : Float) ^ (-(decimal : Nat).toFloat)
                   ∀ i : Fin n, Float.abs (desired.get i - actual.get i) < tolerance) ∧
                  (∀ i : Fin n, Float.abs (actual.get i - desired.get i) = Float.abs (desired.get i - actual.get i)) ∧
                  (actual = desired → result = true) ∧
                  (decimal = 0 → ∀ i : Fin n, Float.abs (desired.get i - actual.get i) < (10 : Float) ^ (-(decimal : Nat).toFloat)) ∧
                  (decimal ≥ 1 → ∀ i : Fin n, Float.abs (desired.get i - actual.get i) < 1.5 * (10 : Float) ^ (-(decimal : Nat).toFloat))⌝⦄ := by
  sorry
