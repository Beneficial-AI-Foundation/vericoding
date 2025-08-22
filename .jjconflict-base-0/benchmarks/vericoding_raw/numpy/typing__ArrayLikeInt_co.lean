/-!
{
  "name": "_ArrayLikeInt_co",
  "category": "Specialized ArrayLike Types",
  "description": "ArrayLike type specialized for integer arrays",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_array_like.py",
  "doc": "A specialized version of ArrayLike that represents objects that can be converted to integer arrays. The '_co' suffix indicates covariance.",
  "code": "_ArrayLikeInt_co = _ArrayLike[\n    Union[\n        bool_,\n        int_,\n        integer[Any],\n        unsignedinteger[Any],\n        signedinteger[Any],\n    ]\n]"
}
-/

-- TODO: Implement _ArrayLikeInt_co
