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
/* helper modified by LLM (iteration 5): modify proof to correctly assert within conditionals */
spec fn get_min_dtype(v: int) -> NumpyDType {
    if v < 0 {
        NumpyDType::Int8
    } else {
        NumpyDType::UInt8
    }
}

proof fn lemma_min_dtype_satisfies(v: int)
    requires
        -128 <= v <= 127
    ensures
        can_represent_value(get_min_dtype(v), v),
        forall|dt: NumpyDType| dtype_size(dt) < dtype_size(get_min_dtype(v)) ==> !can_represent_value(dt, v),
        forall|dt: NumpyDType| dtype_size(dt) == dtype_size(get_min_dtype(v)) && can_represent_value(dt, v) ==> dtype_kind_order(get_min_dtype(v)) <= dtype_kind_order(dt)
{
    let dt_min = get_min_dtype(v);
    assert(can_represent_value(dt_min, v));
    
    // The second ensures holds vacuously since there are no dtypes with size < 8
    
    // Prove the third ensures using if in assert forall
    assert forall|dt: NumpyDType|
        (dtype_size(dt) == 8 && can_represent_value(dt, v))
        implies(dtype_kind_order(dt_min) <= dtype_kind_order(dt)) by {
        if v < 0 {
            // Wait, for if A implies B, actually, since it's assert forall implies(A, B),
            // but to fix, better to use if dtype_size... {
            if dtype_size(dt) == 8 && can_represent_value(dt, v) {
                // Only Int8 can represent
                assert(dt == NumpyDType::Int8);
                assert(dtype_kind_order(dt_min) == 1);
                assert(dtype_kind_order(dt) == 1);
            }
        } else {
            // Both UInt8 and Int8 can represent
            if dtype_size(dt) == 8 && can_represent_value(dt, v) {
                if dt == NumpyDType::UInt8 {
                    assert(dtype_kind_order(dt_min) == 0);
                    assert(dtype_kind_order(dt) == 0);
                } else if dt == NumpyDType::Int8 {
                    assert(dtype_kind_order(dt_min) == 0);
                    assert(dtype_kind_order(dt) == 1);
                }
            }
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
    /* code modified by LLM (iteration 5): modify proof to correctly assert within conditionals */
    let ghost val_int: int = value@ as int;
    let result = if value < 0 {
        NumpyDType::Int8
    } else {
        NumpyDType::UInt8
    };
    proof {
        assert(can_represent_value(result, val_int));
        assert forall|dt: NumpyDType| dtype_size(dt) < dtype_size(result)
            ==> !can_represent_value(dt, val_int) by {
                // No dtypes have size < 8, so condition is vacuous
            };
        assert forall|dt: NumpyDType|
            dtype_size(dt) == dtype_size(result) && can_represent_value(dt, val_int)
            ==> dtype_kind_order(result) <= dtype_kind_order(dt) by {
                if dtype_size(dt) == 8 && can_represent_value(dt, val_int) {
                    if val_int < 0 {
                        assert(dt == NumpyDType::Int8);
                        assert(dtype_kind_order(result) == 1);
                        assert(dtype_kind_order(dt) == 1);
                    } else {
                        if dt == NumpyDType::UInt8 {
                            assert(dtype_kind_order(result) == 0);
                            assert(dtype_kind_order(dt) == 0);
                        } else if dt == NumpyDType::Int8 {
                            assert(dtype_kind_order(result) == 0);
                            assert(dtype_kind_order(dt) == 1);
                        }
                    }
                }
            };
    }
    result
}
// </vc-code>


}

fn main() {}