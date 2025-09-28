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
/* helper modified by LLM (iteration 2): prove that every NumpyDType has size at least 8 bits */
proof fn lemma_dtype_size_min()
    ensures
        forall|dt: NumpyDType| dtype_size(dt) >= 8,
{
    assert forall|dt: NumpyDType| dtype_size(dt) >= 8 by {
        match dt {
            NumpyDType::UInt8 => { assert(8 >= 8); }
            NumpyDType::UInt16 => { assert(16 >= 8); }
            NumpyDType::UInt32 => { assert(32 >= 8); }
            NumpyDType::UInt64 => { assert(64 >= 8); }
            NumpyDType::Int8 => { assert(8 >= 8); }
            NumpyDType::Int16 => { assert(16 >= 8); }
            NumpyDType::Int32 => { assert(32 >= 8); }
            NumpyDType::Int64 => { assert(64 >= 8); }
            NumpyDType::Float16 => { assert(16 >= 8); }
            NumpyDType::Float32 => { assert(32 >= 8); }
            NumpyDType::Float64 => { assert(64 >= 8); }
            NumpyDType::Complex64 => { assert(64 >= 8); }
            NumpyDType::Complex128 => { assert(128 >= 8); }
        }
    };
}
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
    /* code modified by LLM (iteration 2): implement sign-based selection (UInt8 for non-negative, Int8 for negative) and prove postconditions without using int/nat in exec code */
    if value >= 0 {
        proof {
            let vi: int = value as int;
            // Basic bounds for i8 and non-negativity of this branch
            assert(0 <= vi);
            assert(vi <= 127);
            // Result represents the value
            assert(can_represent_value(NumpyDType::UInt8, vi));
            // No smaller dtype can represent (all dtype sizes >= 8)
            lemma_dtype_size_min();
            assert forall|dt: NumpyDType| dtype_size(dt) < dtype_size(NumpyDType::UInt8) ==> !can_represent_value(dt, vi) by {
                assert(dtype_size(NumpyDType::UInt8) == 8);
                assert forall|dt: NumpyDType| dtype_size(dt) < 8 ==> !can_represent_value(dt, vi) by {
                    assert(dtype_size(dt) >= 8);
                }
            };
            // Among equal-size types, UInt8 has minimal kind order
            assert forall|dt: NumpyDType| dtype_size(dt) == dtype_size(NumpyDType::UInt8) && can_represent_value(dt, vi) ==> dtype_kind_order(NumpyDType::UInt8) <= dtype_kind_order(dt) by {
                assert(dtype_size(NumpyDType::UInt8) == 8);
                assert(dtype_kind_order(NumpyDType::UInt8) == 0);
                assert forall|dt: NumpyDType| dtype_size(dt) == 8 && can_represent_value(dt, vi) ==> 0 <= dtype_kind_order(dt) by {
                    // dtype_kind_order returns a nat, hence non-negative
                    assert(0 <= dtype_kind_order(dt));
                }
            };
        }
        NumpyDType::UInt8
    } else {
        proof {
            let vi: int = value as int;
            // Bounds for i8
            assert(-128 <= vi);
            assert(vi <= 127);
            // Result represents the value
            assert(can_represent_value(NumpyDType::Int8, vi));
            // No smaller dtype can represent (all dtype sizes >= 8)
            lemma_dtype_size_min();
            assert forall|dt: NumpyDType| dtype_size(dt) < dtype_size(NumpyDType::Int8) ==> !can_represent_value(dt, vi) by {
                assert(dtype_size(NumpyDType::Int8) == 8);
                assert forall|dt: NumpyDType| dtype_size(dt) < 8 ==> !can_represent_value(dt, vi) by {
                    assert(dtype_size(dt) >= 8);
                }
            };
            // Among equal-size types, ensure Int8 has minimal kind order among representable dtypes
            assert forall|dt: NumpyDType| dtype_size(dt) == dtype_size(NumpyDType::Int8) && can_represent_value(dt, vi) ==> dtype_kind_order(NumpyDType::Int8) <= dtype_kind_order(dt) by {
                assert(dtype_size(NumpyDType::Int8) == 8);
                match dt {
                    NumpyDType::UInt8 => {
                        // vi is negative, so UInt8 cannot represent it
                        assert(!(0 <= vi && vi <= 255));
                    }
                    NumpyDType::Int8 => {
                        assert(dtype_kind_order(NumpyDType::Int8) <= dtype_kind_order(NumpyDType::Int8));
                    }
                    NumpyDType::UInt16 => { assert(dtype_size(dt) == 16); }
                    NumpyDType::UInt32 => { assert(dtype_size(dt) == 32); }
                    NumpyDType::UInt64 => { assert(dtype_size(dt) == 64); }
                    NumpyDType::Int16 => { assert(dtype_size(dt) == 16); }
                    NumpyDType::Int32 => { assert(dtype_size(dt) == 32); }
                    NumpyDType::Int64 => { assert(dtype_size(dt) == 64); }
                    NumpyDType::Float16 => { assert(dtype_size(dt) == 16); }
                    NumpyDType::Float32 => { assert(dtype_size(dt) == 32); }
                    NumpyDType::Float64 => { assert(dtype_size(dt) == 64); }
                    NumpyDType::Complex64 => { assert(dtype_size(dt) == 64); }
                    NumpyDType::Complex128 => { assert(dtype_size(dt) == 128); }
                }
            };
        }
        NumpyDType::Int8
    }
}
// </vc-code>


}

fn main() {}