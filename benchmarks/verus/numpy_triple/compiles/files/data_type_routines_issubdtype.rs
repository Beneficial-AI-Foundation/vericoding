/*
{
  "name": "numpy.issubdtype",
  "category": "Data Type Testing", 
  "description": "Returns True if first argument is a typecode lower/equal in type hierarchy",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.issubdtype.html",
  "doc": "Returns True if first argument is a typecode lower/equal in type hierarchy.\n\nThis is like the builtin issubclass, but for dtypes.\n\nParameters\n----------\narg1, arg2 : dtype_like\n    dtype or object coercible to one.\n\nReturns\n-------\nout : bool\n\nExamples\n--------\n>>> ints = np.array([1, 2, 3], dtype=np.int32)\n>>> np.issubdtype(ints.dtype, np.integer)\nTrue\n>>> np.issubdtype(ints.dtype, np.floating)\nFalse\n>>> floats = np.array([1, 2, 3], dtype=np.float32)\n>>> np.issubdtype(floats.dtype, np.integer)\nFalse\n>>> np.issubdtype(floats.dtype, np.floating)\nTrue\n>>> np.issubdtype(np.float64, np.float32)\nFalse\n>>> np.issubdtype(np.float32, np.float64)\nFalse\n>>> np.issubdtype(np.float64, np.floating)\nTrue\n>>> np.issubdtype(np.float32, np.floating)\nTrue\n>>> np.issubdtype('S1', np.bytes_)\nTrue\n>>> np.issubdtype('i4', np.signedinteger)\nTrue",
}
*/

/* numpy.issubdtype: Returns True if first argument is a typecode lower/equal in type hierarchy.

   This function checks if the first data type is a subtype of the second data type
   in the NumPy type hierarchy. It's similar to Python's built-in issubclass but
   operates on NumPy data types.

   The function implements the NumPy type hierarchy where types are organized
   in a tree structure with 'generic' at the root.
*/

/* Specification: issubdtype returns True if arg1 is a subtype of arg2 in the NumPy type hierarchy.

   Precondition: True (works with any valid NumPy data types)
   Postcondition: The result is True if and only if arg1 is a subtype of arg2 
   according to the NumPy type hierarchy rules.
   
   Key properties:
   1. Reflexivity: Every type is a subtype of itself
   2. Transitivity: If A is subtype of B and B is subtype of C, then A is subtype of C
   3. Hierarchy rules: Specific types are subtypes of their parent categories
   4. Root type: All types are subtypes of 'generic'
*/
use vstd::prelude::*;

verus! {

/* Define a NumPy-like type hierarchy representing the data type system in NumPy */
pub enum NumpyDType {
    /* Generic root type */
    Generic,
    /* Inexact numeric type */
    Inexact,
    /* Floating point type */
    Floating,
    /* 32-bit floating point */
    Float32,
    /* 64-bit floating point */
    Float64,
    /* Numeric type */
    Number,
    /* Integer type */
    Integer,
    /* Signed integer type */
    SignedInteger,
    /* 8-bit signed integer */
    Int8,
    /* 16-bit signed integer */
    Int16,
    /* 32-bit signed integer */
    Int32,
    /* 64-bit signed integer */
    Int64,
    /* Unsigned integer type */
    UnsignedInteger,
    /* 8-bit unsigned integer */
    UInt8,
    /* 16-bit unsigned integer */
    UInt16,
    /* 32-bit unsigned integer */
    UInt32,
    /* 64-bit unsigned integer */
    UInt64,
    /* Character type */
    Character,
    /* Bytes type */
    Bytes,
    /* String type */
    Str,
    /* Boolean type */
    Bool,
}

spec fn dtype_eq(dtype1: NumpyDType, dtype2: NumpyDType) -> bool
{
    match (dtype1, dtype2) {
        (NumpyDType::Generic, NumpyDType::Generic) => true,
        (NumpyDType::Inexact, NumpyDType::Inexact) => true,
        (NumpyDType::Floating, NumpyDType::Floating) => true,
        (NumpyDType::Float32, NumpyDType::Float32) => true,
        (NumpyDType::Float64, NumpyDType::Float64) => true,
        (NumpyDType::Number, NumpyDType::Number) => true,
        (NumpyDType::Integer, NumpyDType::Integer) => true,
        (NumpyDType::SignedInteger, NumpyDType::SignedInteger) => true,
        (NumpyDType::Int8, NumpyDType::Int8) => true,
        (NumpyDType::Int16, NumpyDType::Int16) => true,
        (NumpyDType::Int32, NumpyDType::Int32) => true,
        (NumpyDType::Int64, NumpyDType::Int64) => true,
        (NumpyDType::UnsignedInteger, NumpyDType::UnsignedInteger) => true,
        (NumpyDType::UInt8, NumpyDType::UInt8) => true,
        (NumpyDType::UInt16, NumpyDType::UInt16) => true,
        (NumpyDType::UInt32, NumpyDType::UInt32) => true,
        (NumpyDType::UInt64, NumpyDType::UInt64) => true,
        (NumpyDType::Character, NumpyDType::Character) => true,
        (NumpyDType::Bytes, NumpyDType::Bytes) => true,
        (NumpyDType::Str, NumpyDType::Str) => true,
        (NumpyDType::Bool, NumpyDType::Bool) => true,
        _ => false,
    }
}

/* Define the subtype relation for NumPy types */
spec fn is_sub_dtype(dtype1: NumpyDType, dtype2: NumpyDType) -> bool
{
    if dtype_eq(dtype1, dtype2) {
        true
    } else {
        match (dtype1, dtype2) {
            // Float hierarchy
            (NumpyDType::Float32, NumpyDType::Floating) => true,
            (NumpyDType::Float64, NumpyDType::Floating) => true,
            (NumpyDType::Floating, NumpyDType::Inexact) => true,
            (NumpyDType::Floating, NumpyDType::Number) => true,
            (NumpyDType::Floating, NumpyDType::Generic) => true,
            // Integer hierarchy
            (NumpyDType::Int8, NumpyDType::SignedInteger) => true,
            (NumpyDType::Int16, NumpyDType::SignedInteger) => true,
            (NumpyDType::Int32, NumpyDType::SignedInteger) => true,
            (NumpyDType::Int64, NumpyDType::SignedInteger) => true,
            (NumpyDType::UInt8, NumpyDType::UnsignedInteger) => true,
            (NumpyDType::UInt16, NumpyDType::UnsignedInteger) => true,
            (NumpyDType::UInt32, NumpyDType::UnsignedInteger) => true,
            (NumpyDType::UInt64, NumpyDType::UnsignedInteger) => true,
            (NumpyDType::SignedInteger, NumpyDType::Integer) => true,
            (NumpyDType::UnsignedInteger, NumpyDType::Integer) => true,
            (NumpyDType::Integer, NumpyDType::Number) => true,
            (NumpyDType::Integer, NumpyDType::Generic) => true,
            // Character hierarchy
            (NumpyDType::Str, NumpyDType::Character) => true,
            (NumpyDType::Bytes, NumpyDType::Character) => true,
            (NumpyDType::Character, NumpyDType::Generic) => true,
            // Boolean hierarchy
            (NumpyDType::Bool, NumpyDType::Generic) => true,
            // Number hierarchy
            (NumpyDType::Number, NumpyDType::Generic) => true,
            (NumpyDType::Inexact, NumpyDType::Generic) => true,
            _ => false,
        }
    }
}
// <vc-helpers>
// </vc-helpers>
fn issubdtype(arg1: NumpyDType, arg2: NumpyDType) -> (result: bool)
// <vc-implementation>
{
    return true; // TODO: Remove this line and implement the function body
}
// </vc-implementation>
proof fn issubdtype_spec(arg1: NumpyDType, arg2: NumpyDType)
    ensures 
        is_sub_dtype(arg1, arg2) == is_sub_dtype(arg1, arg2) &&
        // Reflexivity property
        (dtype_eq(arg1, arg2) ==> is_sub_dtype(arg1, arg2) == true) &&
        // Generic is supertype of all types
        (dtype_eq(arg2, NumpyDType::Generic) ==> is_sub_dtype(arg1, arg2) == true) &&
        // Specific hierarchy rules
        (dtype_eq(arg1, NumpyDType::Float32) && dtype_eq(arg2, NumpyDType::Floating) ==> is_sub_dtype(arg1, arg2) == true) &&
        (dtype_eq(arg1, NumpyDType::Float64) && dtype_eq(arg2, NumpyDType::Floating) ==> is_sub_dtype(arg1, arg2) == true) &&
        (dtype_eq(arg1, NumpyDType::Int32) && dtype_eq(arg2, NumpyDType::SignedInteger) ==> is_sub_dtype(arg1, arg2) == true) &&
        (dtype_eq(arg1, NumpyDType::UInt32) && dtype_eq(arg2, NumpyDType::UnsignedInteger) ==> is_sub_dtype(arg1, arg2) == true) &&
        // Non-subtype examples
        (dtype_eq(arg1, NumpyDType::Float32) && dtype_eq(arg2, NumpyDType::Float64) ==> is_sub_dtype(arg1, arg2) == false) &&
        (dtype_eq(arg1, NumpyDType::Float64) && dtype_eq(arg2, NumpyDType::Float32) ==> is_sub_dtype(arg1, arg2) == false) &&
        (dtype_eq(arg1, NumpyDType::Int32) && dtype_eq(arg2, NumpyDType::Floating) ==> is_sub_dtype(arg1, arg2) == false)
// <vc-proof>
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-proof>

fn main() {
}

}