/-!
{
  "name": "_SupportsArray",
  "category": "Protocol Classes",
  "description": "Protocol for objects that implement the __array__ method",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A protocol defining objects that can be converted to NumPy arrays via the __array__ method.\n\nThe _SupportsArray protocol only cares about the default dtype (i.e. dtype=None or no dtype parameter at all) of the to-be returned array. Concrete implementations of the protocol are responsible for adding any and all remaining overloads.",
  "code": "@runtime_checkable\nclass _SupportsArray(Protocol[_DTypeT_co]):\n    def __array__(self) -> np.ndarray[Any, _DTypeT_co]: ..."
}
-/

-- TODO: Implement _SupportsArray
