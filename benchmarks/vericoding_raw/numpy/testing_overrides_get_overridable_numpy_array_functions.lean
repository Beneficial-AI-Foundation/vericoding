/-!
{
  "name": "numpy.testing.overrides.get_overridable_numpy_array_functions",
  "category": "Overrides Module",
  "description": "List all numpy functions overridable via __array_function__",
  "url": "https://numpy.org/doc/stable/reference/testing.overrides.html",
  "doc": "List all numpy functions overridable via \`__array_function__\`.\n\nReturns a set containing all functions in the public numpy API that are overridable via \`__array_function__\`.",
  "code": "def get_overridable_numpy_array_functions():\n    \"\"\"List all numpy functions overridable via \`__array_function__\`\n\n    Parameters\n    ----------\n    None\n\n    Returns\n    -------\n    set\n        A set containing all functions in the public numpy API that are\n        overridable via \`__array_function__\`.\n\n    \"\"\"\n    # 'import numpy' doesn't import recfunctions, so make sure it's imported\n    # so ufuncs defined there show up in the ufunc listing\n    from numpy.lib import recfunctions  # noqa: F401\n    return _array_functions.copy()"
}
-/

-- TODO: Implement get_overridable_numpy_array_functions
