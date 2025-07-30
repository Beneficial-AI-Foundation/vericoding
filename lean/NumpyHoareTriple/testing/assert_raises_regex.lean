/-!
{
  "name": "numpy.testing.assert_raises_regex",
  "category": "Assertion Functions",
  "description": "Fail unless an exception of class exception_class and with message matching expected_regexp is thrown by callable when invoked with arguments args and keyword arguments kwargs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_raises_regex.html",
  "doc": "assert_raises_regex(exception_class, expected_regexp, callable, *args, **kwargs)\nassert_raises_regex(exception_class, expected_regexp)\n\nFail unless an exception of class exception_class and with message matching expected_regexp is thrown by callable when invoked with arguments args and keyword arguments kwargs.\n\nAlternatively, can be used as a context manager.",
  "code": "def assert_raises_regex(exception_class, expected_regexp, *args, **kwargs):\n    \"\"\"\n    assert_raises_regex(exception_class, expected_regexp, callable, *args,\n                        **kwargs)\n    assert_raises_regex(exception_class, expected_regexp)\n\n    Fail unless an exception of class exception_class and with message that\n    matches expected_regexp is thrown by callable when invoked with arguments\n    args and keyword arguments kwargs.\n\n    Alternatively, can be used as a context manager.\n\n    Notes\n    -----\n    .. versionadded:: 1.9.0\n\n    \"\"\"\n    __tracebackhide__ = True  # Hide traceback for py.test\n    return _d.assertRaisesRegex(exception_class, expected_regexp,\n                                *args, **kwargs)"
}
-/

-- TODO: Implement assert_raises_regex
