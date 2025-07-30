/-!
{
  "name": "_ArrayLikeFloat_co",
  "category": "Specialized ArrayLike Types",
  "description": "ArrayLike type specialized for floating-point arrays",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A specialized version of ArrayLike that represents objects that can be converted to floating-point arrays. The '_co' suffix indicates covariance.",
  "code": "_ArrayLikeFloat_co = _ArrayLike[\n    Union[\n        float_,\n        floating[Any],\n        integer[Any],\n        unsignedinteger[Any],\n        signedinteger[Any],\n    ]\n]"
}
-/

-- TODO: Implement _ArrayLikeFloat_co
