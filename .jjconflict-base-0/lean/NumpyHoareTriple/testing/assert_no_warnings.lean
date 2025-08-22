/-!
{
  "name": "numpy.testing.assert_no_warnings",
  "category": "Assertion Functions",
  "description": "Fail if the given callable produces any warnings",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_no_warnings.html",
  "doc": "Fail if the given callable produces any warnings.\n\nIf called with all arguments omitted, may be used as a context manager.",
  "code": "def assert_no_warnings(*args, **kwargs):\n    \"\"\"\n    Fail if the given callable produces any warnings.\n\n    If called with all arguments omitted, may be used as a context manager::\n\n        with assert_no_warnings():\n            do_something()\n\n    The ability to be used as a context manager is new in NumPy v1.11.0.\n\n    Parameters\n    ----------\n    func : callable\n        The callable to test.\n    *args : Arguments\n        Arguments passed to \`func\`.\n    **kwargs : Kwargs\n        Keyword arguments passed to \`func\`.\n\n    Returns\n    -------\n    The value returned by \`func\`.\n\n    \"\"\"\n    with warnings.catch_warnings():\n        warnings.simplefilter('error')\n        if not args and not kwargs:\n            return sys._getframe(0).f_locals\n        else:\n            return args[0](*args[1:], **kwargs)"
}
-/

-- TODO: Implement assert_no_warnings
