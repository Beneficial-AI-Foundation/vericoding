/-!
{
  "name": "_ArrayLikeComplex_co",
  "category": "Specialized ArrayLike Types",
  "description": "ArrayLike type specialized for complex arrays",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A specialized version of ArrayLike that represents objects that can be converted to complex arrays. The '_co' suffix indicates covariance.",
  "code": "_ArrayLikeComplex_co = _ArrayLike[\n    Union[\n        complex_,\n        number[Any],\n        complexfloating[Any],\n    ]\n]"
}
-/

-- TODO: Implement _ArrayLikeComplex_co
