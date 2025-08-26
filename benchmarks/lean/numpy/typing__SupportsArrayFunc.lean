/-!
{
  "name": "_SupportsArrayFunc",
  "category": "Protocol Classes",
  "description": "Protocol for objects that implement the __array_function__ method",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A protocol defining objects that support the NumPy function protocol via __array_function__.\n\nThis allows objects to override the behavior of NumPy functions when they are passed as arguments.",
  "code": "@runtime_checkable\nclass _SupportsArrayFunc(Protocol):\n    def __array_function__(\n        self,\n        func: Callable[..., Any],\n        types: Collection[type[Any]],\n        args: tuple[Any, ...],\n        kwargs: dict[str, Any]\n    ) -> object: ..."
}
-/

-- TODO: Implement _SupportsArrayFunc
