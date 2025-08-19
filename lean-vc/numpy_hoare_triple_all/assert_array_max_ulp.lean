/-!
{
  "name": "numpy.testing.assert_array_max_ulp",
  "category": "Assertion Functions",
  "description": "Check that all items of arrays differ in at most N Units in the Last Place",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_array_max_ulp.html",
  "doc": "Check that all items of arrays differ in at most N Units in the Last Place.\n\nParameters\n----------\na, b : array_like\n    Input arrays to be compared.\nmaxulp : int, optional\n    The maximum number of units in the last place that elements of \`a\` and \`b\` can differ. Default is 1.\ndtype : dtype, optional\n    Data-type to convert \`a\` and \`b\` to if given. Default is None.",
  "code": "def assert_array_max_ulp(a, b, maxulp=1, dtype=None):\n    \"\"\"\n    Check that all items of arrays differ in at most N Units in the Last Place.\n\n    Parameters\n    ----------\n    a, b : array_like\n        Input arrays to be compared.\n    maxulp : int, optional\n        The maximum number of units in the last place that elements of \`a\` and\n        \`b\` can differ. Default is 1.\n    dtype : dtype, optional\n        Data-type to convert \`a\` and \`b\` to if given. Default is None.\n\n    Returns\n    -------\n    ret : ndarray\n        Array containing number of representable floating point numbers between\n        items in \`a\` and \`b\`.\n\n    Raises\n    ------\n    AssertionError\n        If one or more elements differ by more than \`maxulp\`.\n\n    Notes\n    -----\n    For computing the ULP difference, this API does not differentiate between\n    various representations of NAN (ULP difference between 0x7fc00000 and 0xffc00000\n    is zero).\n\n    See Also\n    --------\n    assert_array_almost_equal_nulp : Compare two arrays relative to their\n        spacing.\n\n    Examples\n    --------\n    >>> a = np.linspace(0., 1., 100)\n    >>> res = np.testing.assert_array_max_ulp(a, np.arcsin(np.sin(a)))\n\n    \"\"\"\n    __tracebackhide__ = True  # Hide traceback for py.test\n    import numpy as np\n    ret = nulp_diff(a, b, dtype)\n    if not np.all(ret <= maxulp):\n        raise AssertionError(\"Arrays are not almost equal up to %g ULP\" %\n                             maxulp)\n    return ret"
}
-/

-- TODO: Implement assert_array_max_ulp
