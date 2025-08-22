/-!
{
  "name": "_NestedSequence",
  "category": "Utility Types",
  "description": "Type for nested sequences of arbitrary depth",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_nested_sequence.py",
  "doc": "A generic type representing nested sequences of arbitrary depth. Used internally to type nested lists/sequences that can be converted to arrays.",
  "code": "_T = TypeVar(\"_T\")\n\nclass _NestedSequence(Protocol[_T]):\n    def __len__(self, /) -> int: ...\n    def __getitem__(self, index: int, /) -> _T | _NestedSequence[_T]: ...\n    def __contains__(self, x: object, /) -> bool: ...\n    def __iter__(self, /) -> Iterator[_T | _NestedSequence[_T]]: ...\n    def __reversed__(self, /) -> Iterator[_T | _NestedSequence[_T]]: ..."
}
-/

-- TODO: Implement _NestedSequence
