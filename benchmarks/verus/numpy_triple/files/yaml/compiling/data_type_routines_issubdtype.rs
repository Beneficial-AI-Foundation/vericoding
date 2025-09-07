/* numpy.issubdtype: Returns True if first argument is a typecode lower/equal in type hierarchy.

This function checks if the first data type is a subtype of the second data type
in the NumPy type hierarchy. It's similar to Python's built-in issubclass but
operates on NumPy data types.

The function implements the NumPy type hierarchy where types are organized
in a tree structure with 'generic' at the root.

Specification: issubdtype returns True if arg1 is a subtype of arg2 in the NumPy type hierarchy.

Precondition: True (works with any valid NumPy data types)
Postcondition: The result is True if and only if arg1 is a subtype of arg2 
according to the NumPy type hierarchy rules.

Key properties:
1. Reflexivity: Every type is a subtype of itself
2. Transitivity: If A is subtype of B and B is subtype of C, then A is subtype of C
3. Hierarchy rules: Specific types are subtypes of their parent categories
4. Root type: All types are subtypes of 'generic' */

use vstd::prelude::*;

verus! {

/* Define a NumPy-like type hierarchy representing the data type system in NumPy */
pub enum NumpyDType {
    /* Generic root type */
    Generic,
    /* Inexact numeric type */
    Inexact(Box<NumpyDType>),
    /* Floating point type */
    Floating(Box<NumpyDType>),
    /* 32-bit floating point */
    Float32,
    /* 64-bit floating point */
    Float64,
    /* Numeric type */
    Number(Box<NumpyDType>),
    /* Integer type */
    Integer(Box<NumpyDType>),
    /* Signed integer type */
    SignedInteger(Box<NumpyDType>),
    /* 8-bit signed integer */
    Int8,
    /* 16-bit signed integer */
    Int16,
    /* 32-bit signed integer */
    Int32,
    /* 64-bit signed integer */
    Int64,
    /* Unsigned integer type */
    UnsignedInteger(Box<NumpyDType>),
    /* 8-bit unsigned integer */
    UInt8,
    /* 16-bit unsigned integer */
    UInt16,
    /* 32-bit unsigned integer */
    UInt32,
    /* 64-bit unsigned integer */
    UInt64,
    /* Character type */
    Character(Box<NumpyDType>),
    /* Bytes type */
    Bytes_,
    /* String type */
    Str_,
    /* Boolean type */
    Bool_,
}

/* Define the subtype relation for NumPy types */
spec fn is_sub_dtype_spec(dtype1: NumpyDType, dtype2: NumpyDType) -> bool {
    if dtype1 == dtype2 {
        true
    } else {
        match (dtype1, dtype2) {
            /* Float hierarchy */
            (NumpyDType::Float32, NumpyDType::Floating(_)) => true,
            (NumpyDType::Float64, NumpyDType::Floating(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Inexact(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Number(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Generic) => true,
            /* Integer hierarchy */
            (NumpyDType::Int8, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int16, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int32, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int64, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::UInt8, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt16, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt32, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt64, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::SignedInteger(_), NumpyDType::Integer(_)) => true,
            (NumpyDType::UnsignedInteger(_), NumpyDType::Integer(_)) => true,
            (NumpyDType::Integer(_), NumpyDType::Number(_)) => true,
            (NumpyDType::Integer(_), NumpyDType::Generic) => true,
            /* Character hierarchy */
            (NumpyDType::Str_, NumpyDType::Character(_)) => true,
            (NumpyDType::Bytes_, NumpyDType::Character(_)) => true,
            (NumpyDType::Character(_), NumpyDType::Generic) => true,
            /* Boolean hierarchy */
            (NumpyDType::Bool_, NumpyDType::Generic) => true,
            /* Number hierarchy */
            (NumpyDType::Number(_), NumpyDType::Generic) => true,
            (NumpyDType::Inexact(_), NumpyDType::Generic) => true,
            _ => false,
        }
    }
}
fn issubdtype(arg1: NumpyDType, arg2: NumpyDType) -> (result: bool)
    ensures 
        result == is_sub_dtype_spec(arg1, arg2) &&
        /* Reflexivity property */
        (arg1 == arg2 ==> result == true) &&
        /* Generic is supertype of all types */
        (arg2 == NumpyDType::Generic ==> result == true) &&
        /* Specific hierarchy rules */
        (arg1 == NumpyDType::Float32 && matches!(arg2, NumpyDType::Floating(_)) ==> result == true) &&
        (arg1 == NumpyDType::Float64 && matches!(arg2, NumpyDType::Floating(_)) ==> result == true) &&
        (arg1 == NumpyDType::Int32 && matches!(arg2, NumpyDType::SignedInteger(_)) ==> result == true) &&
        (arg1 == NumpyDType::UInt32 && matches!(arg2, NumpyDType::UnsignedInteger(_)) ==> result == true) &&
        /* Non-subtype examples */
        (arg1 == NumpyDType::Float32 && arg2 == NumpyDType::Float64 ==> result == false) &&
        (arg1 == NumpyDType::Float64 && arg2 == NumpyDType::Float32 ==> result == false) &&
        (arg1 == NumpyDType::Int32 && matches!(arg2, NumpyDType::Floating(_)) ==> result == false)
{
    // impl-start
    assume(false);
    false
    // impl-end
}
}
fn main() {}