/-!
{
  "name": "numpy.testing.overrides.get_overridable_numpy_ufuncs",
  "category": "Overrides Module",
  "description": "List all numpy ufuncs overridable via __array_ufunc__",
  "url": "https://numpy.org/doc/stable/reference/testing.overrides.html",
  "doc": "List all numpy ufuncs overridable via \`__array_ufunc__\`.\n\nReturns a set containing all overridable ufuncs in the public numpy API.",
  "code": "def get_overridable_numpy_ufuncs():\n    \"\"\"List all numpy ufuncs overridable via \`__array_ufunc__\`\n\n    Parameters\n    ----------\n    None\n\n    Returns\n    -------\n    set\n        A set containing all overridable ufuncs in the public numpy API.\n    \"\"\"\n    ufuncs = {obj for obj in _umath.__dict__.values()\n              if isinstance(obj, _ufunc)}\n    return ufuncs"
}
-/

-- TODO: Implement get_overridable_numpy_ufuncs
