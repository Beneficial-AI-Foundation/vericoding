/-!
{
  "name": "_Buffer",
  "category": "Protocol Classes",
  "description": "Protocol for objects that support the buffer protocol",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A protocol defining objects that support the Python buffer protocol.\n\nIn Python 3.12+, this uses collections.abc.Buffer. For earlier versions, it defines a protocol with __buffer__ method.",
  "code": "if sys.version_info >= (3, 12):\n    from collections.abc import Buffer as _Buffer\nelse:\n    @runtime_checkable\n    class _Buffer(Protocol):\n        def __buffer__(self, flags: int, /) -> memoryview: ..."
}
-/

-- TODO: Implement _Buffer
