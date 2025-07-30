/-!
{
  "name": "numpy.testing.assert_raises",
  "category": "Assertion Functions",
  "description": "Fail unless an exception of class exception_class is thrown by callable when invoked with arguments args and keyword arguments kwargs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.assert_raises.html",
  "doc": "assert_raises(exception_class, callable, *args, **kwargs)\nassert_raises(exception_class)\n\nFail unless an exception of class exception_class is thrown by callable when invoked with arguments args and keyword arguments kwargs. If a different type of exception is thrown, it will not be caught, and the test case will be deemed to have suffered an error, exactly as for an unexpected exception.\n\nAlternatively, \`assert_raises\` can be used as a context manager.",
  "code": "def assert_raises(*args, **kwargs):\n    \"\"\"\n    assert_raises(exception_class, callable, *args, **kwargs)\n    assert_raises(exception_class)\n\n    Fail unless an exception of class exception_class is thrown\n    by callable when invoked with arguments args and keyword\n    arguments kwargs. If a different type of exception is\n    thrown, it will not be caught, and the test case will be\n    deemed to have suffered an error, exactly as for an\n    unexpected exception.\n\n    Alternatively, \`assert_raises\` can be used as a context manager:\n\n    >>> from numpy.testing import assert_raises\n    >>> with assert_raises(ZeroDivisionError):\n    ...     1 / 0\n\n    is equivalent to\n\n    >>> def div(x, y):\n    ...     return x / y\n    >>> assert_raises(ZeroDivisionError, div, 1, 0)\n\n    \"\"\"\n    __tracebackhide__ = True  # Hide traceback for py.test\n    return _d.assertRaises(*args, **kwargs)"
}
-/

-- TODO: Implement assert_raises
