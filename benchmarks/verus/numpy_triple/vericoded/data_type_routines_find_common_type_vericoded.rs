// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Data type representation for NumPy types */
#[derive(PartialEq, Eq, Clone, Copy)]
enum DType {
    /* 8-bit signed integer */
    Int8,
    /* 16-bit signed integer */
    Int16,
    /* 32-bit signed integer */
    Int32,
    /* 64-bit signed integer */
    Int64,
    /* 8-bit unsigned integer */
    UInt8,
    /* 16-bit unsigned integer */
    UInt16,
    /* 32-bit unsigned integer */
    UInt32,
    /* 64-bit unsigned integer */
    UInt64,
    /* 32-bit floating point */
    Float32,
    /* 64-bit floating point */
    Float64,
    /* 64-bit complex number */
    Complex64,
    /* 128-bit complex number */
    Complex128,
    /* Boolean type */
    Bool,
    /* Object type */
    Object,
}

/* Type hierarchy for promotion rules */
spec fn dtype_kind(dt: DType) -> char {
    match dt {
        DType::Bool => 'b',
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 => 'i',
        DType::UInt8 | DType::UInt16 | DType::UInt32 | DType::UInt64 => 'u',
        DType::Float32 | DType::Float64 => 'f',
        DType::Complex64 | DType::Complex128 => 'c',
        DType::Object => 'O',
    }
}

/* Type precedence for promotion (higher values have higher precedence) */
spec fn dtype_precedence(dt: DType) -> nat {
    match dt {
        DType::Bool => 0,
        DType::Int8 => 1,
        DType::Int16 => 2,
        DType::Int32 => 3,
        DType::Int64 => 4,
        DType::UInt8 => 5,
        DType::UInt16 => 6,
        DType::UInt32 => 7,
        DType::UInt64 => 8,
        DType::Float32 => 9,
        DType::Float64 => 10,
        DType::Complex64 => 11,
        DType::Complex128 => 12,
        DType::Object => 13,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add exec helper for dtype_precedence */
fn get_dtype_precedence(dt: DType) -> (res: u8)
    ensures res as nat == dtype_precedence(dt),
{
    match dt {
        DType::Bool => 0,
        DType::Int8 => 1,
        DType::Int16 => 2,
        DType::Int32 => 3,
        DType::Int64 => 4,
        DType::UInt8 => 5,
        DType::UInt16 => 6,
        DType::UInt32 => 7,
        DType::UInt64 => 8,
        DType::Float32 => 9,
        DType::Float64 => 10,
        DType::Complex64 => 11,
        DType::Complex128 => 12,
        DType::Object => 13,
    }
}

/* helper modified by LLM (iteration 2): add exec helper for dtype_kind */
fn get_dtype_kind(dt: DType) -> (res: char)
    ensures res == dtype_kind(dt),
{
    match dt {
        DType::Bool => 'b',
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 => 'i',
        DType::UInt8 | DType::UInt16 | DType::UInt32 | DType::UInt64 => 'u',
        DType::Float32 | DType::Float64 => 'f',
        DType::Complex64 | DType::Complex128 => 'c',
        DType::Object => 'O',
    }
}

/* helper modified by LLM (iteration 2): fix compilation error by using exec helper */
fn find_max_precedence_type(types: Vec<DType>) -> (result: DType)
    requires
        types.len() > 0,
    ensures
        types@.contains(result),
        forall|other: DType| types@.contains(other) ==> dtype_precedence(other) <= dtype_precedence(result),
{
    let mut max_type = types[0];
    let mut i: usize = 1;
    while i < types.len()
        invariant
            1 <= i <= types.len(),
            types@.contains(max_type),
            forall|k: int| 0 <= k < i ==> dtype_precedence(types@[k]) <= dtype_precedence(max_type),
        decreases types.len() - i
    {
        if get_dtype_precedence(types[i]) > get_dtype_precedence(max_type) {
            max_type = types[i];
        }
        i = i + 1;
    }
    max_type
}
// </vc-helpers>

// <vc-spec>
fn find_common_type(array_types: Vec<DType>, scalar_types: Vec<DType>) -> (result: Option<DType>)
    requires array_types.len() > 0 || scalar_types.len() > 0,
    ensures 
        /* Case 1: Only array types provided */
        (scalar_types.len() == 0 && array_types.len() > 0) ==> (
            exists|dt: DType| result == Some(dt) &&
            array_types@.contains(dt) &&
            forall|other: DType| array_types@.contains(other) ==> dtype_precedence(other) <= dtype_precedence(dt)
        ),
        /* Case 2: Only scalar types provided */
        (array_types.len() == 0 && scalar_types.len() > 0) ==> (
            exists|dt: DType| result == Some(dt) &&
            scalar_types@.contains(dt) &&
            forall|other: DType| scalar_types@.contains(other) ==> dtype_precedence(other) <= dtype_precedence(dt)
        ),
        /* Case 3: Both array and scalar types provided */
        (array_types.len() > 0 && scalar_types.len() > 0) ==> (
            exists|max_array: DType, max_scalar: DType|
                array_types@.contains(max_array) && scalar_types@.contains(max_scalar) &&
                (forall|dt: DType| array_types@.contains(dt) ==> dtype_precedence(dt) <= dtype_precedence(max_array)) &&
                (forall|dt: DType| scalar_types@.contains(dt) ==> dtype_precedence(dt) <= dtype_precedence(max_scalar)) &&
                ((dtype_kind(max_array) == dtype_kind(max_scalar)) ==> result == Some(max_array)) &&
                ((dtype_kind(max_array) != dtype_kind(max_scalar)) ==> result == Some(max_scalar))
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix compilation error by using exec helper */
{
    if array_types.len() == 0 {
        let max_scalar_type = find_max_precedence_type(scalar_types);
        Some(max_scalar_type)
    } else if scalar_types.len() == 0 {
        let max_array_type = find_max_precedence_type(array_types);
        Some(max_array_type)
    } else {
        let max_array_type = find_max_precedence_type(array_types);
        let max_scalar_type = find_max_precedence_type(scalar_types);

        if get_dtype_kind(max_array_type) == get_dtype_kind(max_scalar_type) {
            Some(max_array_type)
        } else {
            Some(max_scalar_type)
        }
    }
}
// </vc-code>


}
fn main() {}