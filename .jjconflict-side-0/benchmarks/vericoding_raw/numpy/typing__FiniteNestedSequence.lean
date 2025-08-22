/-!
{
  "name": "_FiniteNestedSequence",
  "category": "Utility Types",
  "description": "Type for nested sequences with finite depth",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A type alias representing nested sequences with a finite maximum depth (up to 4 levels). Used to avoid infinite recursion in type definitions.",
  "code": "_FiniteNestedSequence: TypeAlias = (\n    _T\n    | Sequence[_T]\n    | Sequence[Sequence[_T]]\n    | Sequence[Sequence[Sequence[_T]]]\n    | Sequence[Sequence[Sequence[Sequence[_T]]]]\n)"
}
-/

-- TODO: Implement _FiniteNestedSequence
