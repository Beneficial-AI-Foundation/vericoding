/* numpy.promote_types: Returns the data type with the smallest size and smallest scalar kind
to which both type1 and type2 may be safely cast.

This function is symmetric but rarely associative. It returns a "canonical" dtype.

Examples from NumPy documentation:
- promote_types('f4', 'f8') = 'f8' (float64)
- promote_types('i8', 'f4') = 'f8' (float64)
- promote_types('i4', 'S8') = 'S11' (string, but we focus on numeric types)

Specification: promote_types returns the smallest safe common type for two dtypes.

Key properties based on NumPy's type promotion rules:
1. Symmetry: promote_types(a, b) = promote_types(b, a)
2. Safety: Both input types can be safely cast to the result type
3. Minimality: The result is the smallest type that satisfies the safety requirement
4. Type promotion hierarchy: 
   - If either input is complex, result is complex
   - If either input is float, result is float (unless both are complex)
   - Signed integers promote to larger signed integers
   - Unsigned integers promote to larger unsigned integers
   - Mixed signed/unsigned promote to signed of sufficient size
5. Size consideration: Result has size >= max(size(type1), size(type2))
6. Specific examples:
   - Float32 + Float64 → Float64 (larger precision)
   - Int64 + Float32 → Float64 (float with sufficient precision)
   - Complex64 + Float32 → Complex64 (complex dominates) */

use vstd::prelude::*;

verus! {

/* Define enumeration for NumPy data types */
#[derive(Eq, PartialEq)]
enum NumpyDType {
    UInt8,      /* 8-bit unsigned integer */
    UInt16,     /* 16-bit unsigned integer */
    UInt32,     /* 32-bit unsigned integer */
    UInt64,     /* 64-bit unsigned integer */
    Int8,       /* 8-bit signed integer */
    Int16,      /* 16-bit signed integer */
    Int32,      /* 32-bit signed integer */
    Int64,      /* 64-bit signed integer */
    Float16,    /* 16-bit floating point */
    Float32,    /* 32-bit floating point */
    Float64,    /* 64-bit floating point */
    Complex64,  /* 64-bit complex number */
    Complex128, /* 128-bit complex number */
}

/* Define type sizes in bits */
spec fn dtype_size(dt: NumpyDType) -> nat {
    match dt {
        NumpyDType::UInt8 => 8,
        NumpyDType::UInt16 => 16,
        NumpyDType::UInt32 => 32,
        NumpyDType::UInt64 => 64,
        NumpyDType::Int8 => 8,
        NumpyDType::Int16 => 16,
        NumpyDType::Int32 => 32,
        NumpyDType::Int64 => 64,
        NumpyDType::Float16 => 16,
        NumpyDType::Float32 => 32,
        NumpyDType::Float64 => 64,
        NumpyDType::Complex64 => 64,
        NumpyDType::Complex128 => 128,
    }
}
/* Define type promotion rules hierarchy */
spec fn promotion_hierarchy(dt: NumpyDType) -> nat {
    match dt {
        NumpyDType::UInt8 => 0,
        NumpyDType::UInt16 => 1,
        NumpyDType::UInt32 => 2,
        NumpyDType::UInt64 => 3,
        NumpyDType::Int8 => 4,
        NumpyDType::Int16 => 5,
        NumpyDType::Int32 => 6,
        NumpyDType::Int64 => 7,
        NumpyDType::Float16 => 8,
        NumpyDType::Float32 => 9,
        NumpyDType::Float64 => 10,
        NumpyDType::Complex64 => 11,
        NumpyDType::Complex128 => 12,
    }
}
/* Check if a type is a signed integer */
spec fn is_signed_integer(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64 => true,
        _ => false,
    }
}
/* Check if a type is an unsigned integer */
spec fn is_unsigned_integer(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64 => true,
        _ => false,
    }
}
/* Check if a type is a floating point type */
spec fn is_float(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64 => true,
        _ => false,
    }
}
/* Check if a type is a complex type */
spec fn is_complex(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::Complex64 | NumpyDType::Complex128 => true,
        _ => false,
    }
}
spec fn promote_types_spec(type1: NumpyDType, type2: NumpyDType) -> NumpyDType;

fn promote_types(type1: NumpyDType, type2: NumpyDType) -> (result: NumpyDType)
    ensures
        result == promote_types_spec(type1, type2),
        
        /* Symmetry property - function is commutative */
        promote_types_spec(type1, type2) == promote_types_spec(type2, type1),
        
        /* Type promotion hierarchy rules */
        /* If either input is complex, result must be complex */
        (is_complex(type1) || is_complex(type2)) ==> is_complex(result),
        
        /* If either input is float (and not complex), result is float or complex */
        (is_float(type1) || is_float(type2)) ==> (is_float(result) || is_complex(result)),
        
        /* Size constraint: result size >= max of input sizes */
        dtype_size(result) >= dtype_size(type1) && dtype_size(result) >= dtype_size(type2),
        
        /* Promotion hierarchy: result rank >= max of input ranks */
        promotion_hierarchy(result) >= promotion_hierarchy(type1) && promotion_hierarchy(result) >= promotion_hierarchy(type2),
        
        /* Safety constraints: both input types can be safely cast to result */
        /* Complex types can hold any numeric value */
        is_complex(result) ==> (
            (is_complex(type1) || is_float(type1) || is_signed_integer(type1) || is_unsigned_integer(type1)) &&
            (is_complex(type2) || is_float(type2) || is_signed_integer(type2) || is_unsigned_integer(type2))
        ),
        
        /* Float types can hold integers and smaller floats */
        (is_float(result) && !is_complex(result)) ==> (
            (!is_complex(type1) && !is_complex(type2)) &&
            (dtype_size(result) >= dtype_size(type1) || !is_float(type1)) &&
            (dtype_size(result) >= dtype_size(type2) || !is_float(type2))
        ),
        
        /* Specific promotion rules for common cases from NumPy documentation */
        /* Integer + Float → Float with sufficient precision (like 'i8' + 'f4' → 'f8') */
        ((is_signed_integer(type1) || is_unsigned_integer(type1)) && is_float(type2)) ==> (
            is_float(result) && dtype_size(result) >= dtype_size(type2)
        ),
        
        /* Float + Integer → Float with sufficient precision */
        (is_float(type1) && (is_signed_integer(type2) || is_unsigned_integer(type2))) ==> (
            is_float(result) && dtype_size(result) >= dtype_size(type1)
        ),
        
        /* Complex + any non-complex → Complex with sufficient precision */
        (is_complex(type1) && !is_complex(type2)) ==> (
            is_complex(result) && dtype_size(result) >= dtype_size(type1)
        ),
        (is_complex(type2) && !is_complex(type1)) ==> (
            is_complex(result) && dtype_size(result) >= dtype_size(type2)
        ),
        
        /* Same types promote to themselves (reflexivity) */
        (type1 == type2) ==> (result == type1),
        
        /* Float precision promotion (like 'f4' + 'f8' → 'f8') */
        (is_float(type1) && is_float(type2)) ==> (
            is_float(result) && 
            dtype_size(result) >= dtype_size(type1) && 
            dtype_size(result) >= dtype_size(type2)
        ),
{
    // impl-start
    assume(false);
    NumpyDType::UInt8
    // impl-end
}
}
fn main() {}