// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum CastingRule {
    No,
    Equiv,
    Safe,
    SameKind,
    Unrestricted,
}

#[derive(PartialEq, Eq)]
pub enum DType {
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
    Complex64,
    Complex128,
    Bool,
}
// </vc-preamble>

// <vc-helpers>
fn dtypes_are_equal(a: DType, b: DType) -> (res: bool)
    ensures res <==> a == b
{
    match a {
        DType::Int8 => matches!(b, DType::Int8),
        DType::Int16 => matches!(b, DType::Int16),
        DType::Int32 => matches!(b, DType::Int32),
        DType::Int64 => matches!(b, DType::Int64),
        DType::Float32 => matches!(b, DType::Float32),
        DType::Float64 => matches!(b, DType::Float64),
        DType::Complex64 => matches!(b, DType::Complex64),
        DType::Complex128 => matches!(b, DType::Complex128),
        DType::Bool => matches!(b, DType::Bool),
    }
}

fn is_int(dtype: DType) -> (res: bool)
    ensures res <==> (dtype == DType::Int8 || dtype == DType::Int16 || dtype == DType::Int32 || dtype == DType::Int64)
{
    matches!(dtype, DType::Int8) || matches!(dtype, DType::Int16) || matches!(dtype, DType::Int32) || matches!(dtype, DType::Int64)
}

fn is_float(dtype: DType) -> (res: bool)
    ensures res <==> (dtype == DType::Float32 || dtype == DType::Float64)
{
    matches!(dtype, DType::Float32) || matches!(dtype, DType::Float64)
}

fn is_complex(dtype: DType) -> (res: bool)
    ensures res <==> (dtype == DType::Complex64 || dtype == DType::Complex128)
{
    matches!(dtype, DType::Complex64) || matches!(dtype, DType::Complex128)
}

/* helper modified by LLM (iteration 5): expanded ensures clause to fix compilation error */
fn can_safe_cast(from_dtype: DType, to_dtype: DType) -> (result: bool)
    ensures
        result <==> (
            (from_dtype == to_dtype) ||
            ((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) &&
             (to_dtype == DType::Int8 || to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64) &&
             (
                (from_dtype == DType::Int8 && (to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
                (from_dtype == DType::Int16 && (to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
                (from_dtype == DType::Int32 && to_dtype == DType::Int64)
            )) ||
            ((from_dtype == DType::Float32 || from_dtype == DType::Float64) &&
             (to_dtype == DType::Float32 || to_dtype == DType::Float64) &&
             (from_dtype == DType::Float32 && to_dtype == DType::Float64)) ||
            ((from_dtype == DType::Complex64 || from_dtype == DType::Complex128) &&
             (to_dtype == DType::Complex64 || to_dtype == DType::Complex128) &&
             (from_dtype == DType::Complex64 && to_dtype == DType::Complex128)) ||
            ((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) &&
             (to_dtype == DType::Float32 || to_dtype == DType::Float64) &&
             (
                ((from_dtype == DType::Int8 || from_dtype == DType::Int16) && (to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
                (from_dtype == DType::Int32 && to_dtype == DType::Float64)
            )) ||
            ((from_dtype == DType::Float32 || from_dtype == DType::Float64) &&
             (to_dtype == DType::Complex64 || to_dtype == DType::Complex128))
        )
{
    if dtypes_are_equal(from_dtype, to_dtype) {
        return true;
    }

    let from_is_int = is_int(from_dtype);
    let to_is_int = is_int(to_dtype);
    let from_is_float = is_float(from_dtype);
    let to_is_float = is_float(to_dtype);
    let from_is_complex = is_complex(from_dtype);
    let to_is_complex = is_complex(to_dtype);

    if from_is_int && to_is_int {
        (matches!(from_dtype, DType::Int8) && (matches!(to_dtype, DType::Int16) || matches!(to_dtype, DType::Int32) || matches!(to_dtype, DType::Int64))) ||
        (matches!(from_dtype, DType::Int16) && (matches!(to_dtype, DType::Int32) || matches!(to_dtype, DType::Int64))) ||
        (matches!(from_dtype, DType::Int32) && matches!(to_dtype, DType::Int64))
    } else if from_is_float && to_is_float {
        matches!(from_dtype, DType::Float32) && matches!(to_dtype, DType::Float64)
    } else if from_is_complex && to_is_complex {
        matches!(from_dtype, DType::Complex64) && matches!(to_dtype, DType::Complex128)
    } else if from_is_int && to_is_float {
        ((matches!(from_dtype, DType::Int8) || matches!(from_dtype, DType::Int16)) && (matches!(to_dtype, DType::Float32) || matches!(to_dtype, DType::Float64))) ||
        (matches!(from_dtype, DType::Int32) && matches!(to_dtype, DType::Float64))
    } else if from_is_float && to_is_complex {
        true
    } else {
        false
    }
}

/* helper modified by LLM (iteration 5): expanded ensures clause to fix compilation error */
fn can_same_kind_cast(from_dtype: DType, to_dtype: DType) -> (result: bool)
    ensures
        result <==> (
            ((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) &&
             (to_dtype == DType::Int8 || to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
            ((from_dtype == DType::Float32 || from_dtype == DType::Float64) &&
             (to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
            ((from_dtype == DType::Complex64 || from_dtype == DType::Complex128) &&
             (to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||
            ((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) &&
             ((to_dtype == DType::Float32 || to_dtype == DType::Float64) ||
              (to_dtype == DType::Complex64 || to_dtype == DType::Complex128))) ||
            ((from_dtype == DType::Float32 || from_dtype == DType::Float64) &&
             (to_dtype == DType::Complex64 || to_dtype == DType::Complex128))
        )
{
    let from_is_int = is_int(from_dtype);
    let from_is_float = is_float(from_dtype);
    let from_is_complex = is_complex(from_dtype);
    let to_is_int = is_int(to_dtype);
    let to_is_float = is_float(to_dtype);
    let to_is_complex = is_complex(to_dtype);

    (from_is_int && to_is_int) ||
    (from_is_float && to_is_float) ||
    (from_is_complex && to_is_complex) ||
    (from_is_int && (to_is_float || to_is_complex)) ||
    (from_is_float && to_is_complex)
}
// </vc-helpers>

// <vc-spec>
fn can_cast(from_dtype: DType, to_dtype: DType, casting: CastingRule) -> (result: bool)
    ensures

        (from_dtype == to_dtype ==> result == true) &&

        (casting == CastingRule::No ==> (result == true <==> from_dtype == to_dtype)) &&

        (casting == CastingRule::Safe ==> 
            (result == true ==> 

                ((from_dtype == DType::Int8 && (to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
                 (from_dtype == DType::Int16 && (to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
                 (from_dtype == DType::Int32 && to_dtype == DType::Int64) ||

                 (from_dtype == DType::Float32 && to_dtype == DType::Float64) ||

                 ((from_dtype == DType::Int8 || from_dtype == DType::Int16) && (to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
                 (from_dtype == DType::Int32 && to_dtype == DType::Float64) ||

                 (from_dtype == DType::Complex64 && to_dtype == DType::Complex128) ||

                 ((from_dtype == DType::Float32 || from_dtype == DType::Float64) && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||

                 (from_dtype == to_dtype)))) &&

        (casting == CastingRule::SameKind ==> 
            (result == true ==> 

                (((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) && 
                  (to_dtype == DType::Int8 || to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||

                 ((from_dtype == DType::Float32 || from_dtype == DType::Float64) && 
                  (to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||

                 ((from_dtype == DType::Complex64 || from_dtype == DType::Complex128) && 
                  (to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||

                 ((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) && 
                  (to_dtype == DType::Float32 || to_dtype == DType::Float64 || to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||
                 ((from_dtype == DType::Float32 || from_dtype == DType::Float64) && 
                  (to_dtype == DType::Complex64 || to_dtype == DType::Complex128))))) &&

        (casting == CastingRule::Unrestricted ==> result == true) &&

        (casting == CastingRule::Equiv ==> (result == true <==> from_dtype == to_dtype))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no logical changes, but helpers modified to fix compilation */
    if dtypes_are_equal(from_dtype, to_dtype) {
        return true;
    }

    match casting {
        CastingRule::No => {
            false
        }
        CastingRule::Equiv => {
            false
        }
        CastingRule::Safe => {
            can_safe_cast(from_dtype, to_dtype)
        }
        CastingRule::SameKind => {
            can_same_kind_cast(from_dtype, to_dtype)
        }
        CastingRule::Unrestricted => {
            true
        }
    }
}
// </vc-code>

}
fn main() {}