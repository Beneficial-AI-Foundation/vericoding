import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.sctype2char",
  "category": "Miscellaneous Type Utilities",
  "description": "Return the string representation of a scalar dtype",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.sctype2char.html",
  "doc": "Return the string representation of a scalar dtype.\n\nParameters\n----------\nsctype : scalar dtype or object\n    If a scalar dtype, the corresponding string character is returned. If an object, sctype2char tries to infer its scalar type and then return the corresponding string character.\n\nReturns\n-------\ntypechar : str\n    The string character corresponding to the scalar type.\n\nRaises\n------\nValueError\n    If sctype is an object for which the type cannot be inferred.\n\nExamples\n--------\n>>> for sctype in [np.int32, np.double, np.complex_, np.bytes_, np.ndarray]:\n...     print(np.sctype2char(sctype))\n...\nl\nd\nD\nS\nO\n\n>>> x = np.array([1., 2-1.j])\n>>> np.sctype2char(x)\n'D'\n>>> np.sctype2char(list)\n'O'",
  "code": "\n@set_module('numpy')\ndef sctype2char(sctype):\n    \"\"\"\n    Return the string representation of a scalar dtype.\n\n    Parameters\n    ----------\n    sctype : scalar dtype or object\n        If a scalar dtype, the corresponding string character is\n        returned. If an object, \`\`sctype2char\`\` tries to infer its scalar type\n        and then return the corresponding string character.\n\n    Returns\n    -------\n    typechar : str\n        The string character corresponding to the scalar type.\n\n    Raises\n    ------\n    ValueError\n        If \`sctype\` is an object for which the type cannot be inferred.\n\n    See Also\n    --------\n    obj2sctype, issctype, issubsctype, mintypecode\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> for sctype in [np.int32, np.double, np.complex_, np.bytes_, np.ndarray]:\n    ...     print(np.sctype2char(sctype))\n    l # may vary\n    d\n    D\n    S\n    O\n\n    >>> x = np.array([1., 2-1.j])\n    >>> np.sctype2char(x)\n    'D'\n    >>> np.sctype2char(list)\n    'O'\n\n    \"\"\"\n    sctype = obj2sctype(sctype)\n    if sctype is None:\n        raise ValueError(\"unrecognized type\")\n    if sctype not in sctypeDict.values():\n        # catches void, void pointer and user-defined structured dtypes\n        raise KeyError(sctype)\n    return dtype(sctype).char"
}
-/

/-- Scalar data type enumeration for numpy types -/
inductive ScalarType
  | /-- 32-bit signed integer -/ int32
  | /-- 64-bit signed integer -/ int64
  | /-- 32-bit floating point -/ float32
  | /-- 64-bit floating point -/ float64
  | /-- 64-bit complex number -/ complex64
  | /-- 128-bit complex number -/ complex128
  | /-- Byte string -/ bytes
  | /-- Generic object -/ object

/-- numpy.sctype2char: Return the string representation of a scalar dtype
    
    Converts a scalar data type to its corresponding single-character string representation.
    This is used internally by numpy to represent data types in a compact form.
    
    The mapping follows numpy's dtype.char convention:
    - int32 → 'l'
    - float64 (double) → 'd'  
    - complex128 → 'D'
    - bytes → 'S'
    - object → 'O'
-/
def sctype2char (sctype : ScalarType) : Id String :=
  sorry

/-- Specification: sctype2char returns the correct character representation
    for each scalar type.
    
    Precondition: Valid scalar type (guaranteed by type system)
    Postcondition: Returns the standard numpy character for the given type
-/
theorem sctype2char_spec (sctype : ScalarType) :
    ⦃⌜True⌝⦄
    sctype2char sctype
    ⦃⇓result => ⌜
      (sctype = ScalarType.int32 → result = "l") ∧
      (sctype = ScalarType.int64 → result = "q") ∧
      (sctype = ScalarType.float32 → result = "f") ∧
      (sctype = ScalarType.float64 → result = "d") ∧
      (sctype = ScalarType.complex64 → result = "F") ∧
      (sctype = ScalarType.complex128 → result = "D") ∧
      (sctype = ScalarType.bytes → result = "S") ∧
      (sctype = ScalarType.object → result = "O")
    ⌝⦄ := by
  sorry