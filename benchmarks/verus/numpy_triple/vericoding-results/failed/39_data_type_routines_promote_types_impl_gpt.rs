// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum NumpyDType {
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Int8,
    Int16,
    Int32,
    Int64,
    Float16,
    Float32,
    Float64,
    Complex64,
    Complex128,
}

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

spec fn is_signed_integer(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64 => true,
        _ => false,
    }
}

spec fn is_unsigned_integer(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64 => true,
        _ => false,
    }
}

spec fn is_float(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64 => true,
        _ => false,
    }
}

spec fn is_complex(dt: NumpyDType) -> bool {
    match dt {
        NumpyDType::Complex64 | NumpyDType::Complex128 => true,
        _ => false,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer classification helper (kept minimal to avoid duplicate spec definitions) */
spec fn is_integer(dt: NumpyDType) -> bool { is_signed_integer(dt) || is_unsigned_integer(dt) }
// </vc-helpers>

// <vc-spec>
spec fn promote_types_spec(type1: NumpyDType, type2: NumpyDType) -> NumpyDType;

fn promote_types(type1: NumpyDType, type2: NumpyDType) -> (result: NumpyDType)
    ensures
        result == promote_types_spec(type1, type2),

        promote_types_spec(type1, type2) == promote_types_spec(type2, type1),

        (is_complex(type1) || is_complex(type2)) ==> is_complex(result),

        (is_float(type1) || is_float(type2)) ==> (is_float(result) || is_complex(result)),

        dtype_size(result) >= if dtype_size(type1) >= dtype_size(type2) { dtype_size(type1) } else { dtype_size(type2) },

        promotion_hierarchy(result) >= if promotion_hierarchy(type1) >= promotion_hierarchy(type2) { promotion_hierarchy(type1) } else { promotion_hierarchy(type2) },

        (type1 == type2) ==> (result == type1),

        (is_float(type1) && is_float(type2)) ==> (
            is_float(result) && dtype_size(result) >= if dtype_size(type1) >= dtype_size(type2) { dtype_size(type1) } else { dtype_size(type2) }
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement promotion logic directly without redefining spec; compute result using variant-based rules */
    let res = if is_complex(type1) || is_complex(type2) {
        if type1 == NumpyDType::Complex128 || type2 == NumpyDType::Complex128 {
            NumpyDType::Complex128
        } else {
            NumpyDType::Complex64
        }
    } else if is_float(type1) || is_float(type2) {
        if type1 == NumpyDType::Float64 || type2 == NumpyDType::Float64
            || type1 == NumpyDType::Int64 || type2 == NumpyDType::Int64
            || type1 == NumpyDType::UInt64 || type2 == NumpyDType::UInt64 {
            NumpyDType::Float64
        } else if type1 == NumpyDType::Float32 || type2 == NumpyDType::Float32
            || type1 == NumpyDType::Int32 || type2 == NumpyDType::Int32
            || type1 == NumpyDType::UInt32 || type2 == NumpyDType::UInt32 {
            NumpyDType::Float32
        } else {
            NumpyDType::Float16
        }
    } else {
        if is_signed_integer(type1) || is_signed_integer(type2) {
            if type1 == NumpyDType::Int64 || type2 == NumpyDType::Int64
                || type1 == NumpyDType::UInt64 || type2 == NumpyDType::UInt64 {
                NumpyDType::Int64
            } else if type1 == NumpyDType::Int32 || type2 == NumpyDType::Int32
                || type1 == NumpyDType::UInt32 || type2 == NumpyDType::UInt32 {
                NumpyDType::Int32
            } else if type1 == NumpyDType::Int16 || type2 == NumpyDType::Int16
                || type1 == NumpyDType::UInt16 || type2 == NumpyDType::UInt16 {
                NumpyDType::Int16
            } else {
                NumpyDType::Int8
            }
        } else {
            if type1 == NumpyDType::UInt64 || type2 == NumpyDType::UInt64 {
                NumpyDType::UInt64
            } else if type1 == NumpyDType::UInt32 || type2 == NumpyDType::UInt32 {
                NumpyDType::UInt32
            } else if type1 == NumpyDType::UInt16 || type2 == NumpyDType::UInt16 {
                NumpyDType::UInt16
            } else {
                NumpyDType::UInt8
            }
        }
    };

    res
}
// </vc-code>

}
fn main() {}