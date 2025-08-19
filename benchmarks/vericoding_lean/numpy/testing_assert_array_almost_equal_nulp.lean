/-!
{
  "name": "numpy.testing.assert_array_almost_equal_nulp",
  "category": "Assertion Functions",
  "description": "Compare two arrays relative to their spacing",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_array_almost_equal_nulp.html",
  "doc": "Compare two arrays relative to their spacing.\n\nThis is a relatively robust method to compare two arrays whose amplitude is variable.",
  "code": "def assert_array_almost_equal_nulp(x, y, nulp=1):\n    \"\"\"\n    Compare two arrays relative to their spacing.\n\n    This is a relatively robust method to compare two arrays whose amplitude\n    is variable.\n\n    Parameters\n    ----------\n    x, y : array_like\n        Input arrays.\n    nulp : int, optional\n        The maximum number of unit in the last place for tolerance (see Notes).\n        Default is 1.\n\n    Returns\n    -------\n    None\n\n    Raises\n    ------\n    AssertionError\n        If the spacing between \`x\` and \`y\` for one or more elements is larger\n        than \`nulp\`.\n\n    See Also\n    --------\n    assert_array_max_ulp : Check that all items of arrays differ in at most\n        N Units in the Last Place.\n    spacing : Return the distance between x and the nearest adjacent number.\n\n    Notes\n    -----\n    An assertion is raised if the following condition is not met::\n\n        abs(x - y) <= nulp * spacing(maximum(abs(x), abs(y)))\n\n    Examples\n    --------\n    >>> x = np.array([1., 1e-10, 1e-20])\n    >>> eps = np.finfo(x.dtype).eps\n    >>> np.testing.assert_array_almost_equal_nulp(x, x*eps/2 + x)\n\n    >>> np.testing.assert_array_almost_equal_nulp(x, x*eps + x)\n    Traceback (most recent call last):\n        ...\n    AssertionError: X and Y are not equal to 1 ULP (max is 2)\n\n    \"\"\"\n    __tracebackhide__ = True  # Hide traceback for py.test\n    import numpy as np\n    ax = np.abs(x)\n    ay = np.abs(y)\n    ref = nulp * np.spacing(np.where(ax > ay, ax, ay))\n    if not np.all(np.abs(x-y) <= ref):\n        if np.iscomplexobj(x) or np.iscomplexobj(y):\n            msg = \"X and Y are not equal to %d ULP\" % nulp\n        else:\n            max_nulp = np.max(nulp_diff(x, y))\n            msg = \"X and Y are not equal to %d ULP (max is %g)\" % (nulp, max_nulp)\n        raise AssertionError(msg)"
}
-/

-- TODO: Implement assert_array_almost_equal_nulp
