// <vc-preamble>
use vstd::prelude::*;

verus! {
/* Enumeration for NumPy data types */
#[derive(PartialEq, Eq, Structural)]
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

/* Define type hierarchy (order of preference) */
spec fn dtype_kind_order(dt: NumpyDType) -> nat {
    match dt {
        NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64 => 0,
        NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64 => 1,
        NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64 => 2,
        NumpyDType::Complex64 | NumpyDType::Complex128 => 3,
    }
}

/* Check if a type can represent a given integer value */
spec fn can_represent_value(dt: NumpyDType, value: int) -> bool {
    match dt {
        NumpyDType::UInt8 => 0 <= value <= 255,
        NumpyDType::UInt16 => 0 <= value <= 65535,
        NumpyDType::UInt32 => 0 <= value <= 4294967295,
        NumpyDType::UInt64 => 0 <= value <= 18446744073709551615,
        NumpyDType::Int8 => -128 <= value <= 127,
        NumpyDType::Int16 => -32768 <= value <= 32767,
        NumpyDType::Int32 => -2147483648 <= value <= 2147483647,
        NumpyDType::Int64 => -9223372036854775808 <= value <= 9223372036854775807,
        NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64 | NumpyDType::Complex64 | NumpyDType::Complex128 => true,
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_scalar_type(value: i8) -> (result: NumpyDType)
    ensures
        can_represent_value(result, value as int),
        forall|dt: NumpyDType| dtype_size(dt) < dtype_size(result) ==> !can_represent_value(dt, value as int),
        forall|dt: NumpyDType| dtype_size(dt) == dtype_size(result) && can_represent_value(dt, value as int) ==> dtype_kind_order(result) <= dtype_kind_order(dt)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}