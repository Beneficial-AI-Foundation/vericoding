/-!
{
  "name": "numpy.testing.overrides.allows_array_ufunc_override",
  "category": "Overrides Module",
  "description": "Determine if a function can be overridden via __array_ufunc__",
  "url": "https://numpy.org/doc/stable/reference/testing.overrides.html",
  "doc": "Determine if a function can be overridden via \`__array_ufunc__\`.\n\nThis function is equivalent to \`\`isinstance(func, np.ufunc)\`\` and will work correctly for ufuncs defined outside of Numpy.",
  "code": "def allows_array_ufunc_override(func):\n    \"\"\"Determine if a function can be overridden via \`__array_ufunc__\`\n\n    Parameters\n    ----------\n    func : callable\n        Function that may be overridable via \`__array_ufunc__\`\n\n    Returns\n    -------\n    bool\n        \`True\` if \`func\` is overridable via \`__array_ufunc__\` and\n        \`False\` otherwise.\n\n    Notes\n    -----\n    This function is equivalent to \`\`isinstance(func, np.ufunc)\`\` and\n    will work correctly for ufuncs defined outside of Numpy.\n\n    \"\"\"\n    return isinstance(func, _ufunc)"
}
-/

-- TODO: Implement allows_array_ufunc_override
