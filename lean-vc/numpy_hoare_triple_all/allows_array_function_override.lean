/-!
{
  "name": "numpy.testing.overrides.allows_array_function_override",
  "category": "Overrides Module",
  "description": "Determine if a Numpy function can be overridden via __array_function__",
  "url": "https://numpy.org/doc/stable/reference/testing.overrides.html",
  "doc": "Determine if a Numpy function can be overridden via \`__array_function__\`.\n\nReturns True if \`func\` is a function in the Numpy API that is overridable via \`__array_function__\` and False otherwise.",
  "code": "def allows_array_function_override(func):\n    \"\"\"Determine if a Numpy function can be overridden via \`__array_function__\`\n\n    Parameters\n    ----------\n    func : callable\n        Function that may be overridable via \`__array_function__\`\n\n    Returns\n    -------\n    bool\n        \`True\` if \`func\` is a function in the Numpy API that is\n        overridable via \`__array_function__\` and \`False\` otherwise.\n    \"\"\"\n    return func in _array_functions"
}
-/

-- TODO: Implement allows_array_function_override
