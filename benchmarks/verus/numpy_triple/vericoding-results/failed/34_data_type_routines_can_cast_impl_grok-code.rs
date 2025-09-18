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
/* helper modified by LLM (iteration 4): Changed helper function parameters to &DType to avoid move errors */
fn is_int8(d: &DType) -> bool {
    match d {
        DType::Int8 => true,
        _ => false,
    }
}

fn is_int16(d: &DType) -> bool {
    match d {
        DType::Int16 => true,
        _ => false,
    }
}

fn is_int32(d: &DType) -> bool {
    match d {
        DType::Int32 => true,
        _ => false,
    }
}

fn is_int64(d: &DType) -> bool {
    match d {
        DType::Int64 => true,
        _ => false,
    }
}

fn is_float32(d: &DType) -> bool {
    match d {
        DType::Float32 => true,
        _ => false,
    }
}

fn is_float64(d: &DType) -> bool {
    match d {
        DType::Float64 => true,
        _ => false,
    }
}

fn is_complex64(d: &DType) -> bool {
    match d {
        DType::Complex64 => true,
        _ => false,
    }
}

fn is_complex128(d: &DType) -> bool {
    match d {
        DType::Complex128 => true,
        _ => false,
    }
}

fn is_bool(d: &DType) -> bool {
    match d {
        DType::Bool => true,
        _ => false,
    }
}

fn eq_dtype(a: &DType, b: &DType) -> bool {
    match (a, b) {
        (DType::Int8, DType::Int8) => true,
        (DType::Int16, DType::Int16) => true,
        (DType::Int32, DType::Int32) => true,
        (DType::Int64, DType::Int64) => true,
        (DType::Float32, DType::Float32) => true,
        (DType::Float64, DType::Float64) => true,
        (DType::Complex64, DType::Complex64) => true,
        (DType::Complex128, DType::Complex128) => true,
        (DType::Bool, DType::Bool) => true,
        _ => false,
    }
}

fn is_safe(from: &DType, to: &DType) -> bool {
    if is_int8(&from) && (is_int16(&to) || is_int32(&to) || is_int64(&to)) {
        true
    } else if is_int16(&from) && (is_int32(&to) || is_int64(&to)) {
        true
    } else if is_int32(&from) && is_int64(&to) {
        true
    } else if is_float32(&from) && is_float64(&to) {
        true
    } else if (is_int8(&from) || is_int16(&from)) && (is_float32(&to) || is_float64(&to)) {
        true
    } else if is_int32(&from) && is_float64(&to) {
        true
    } else if is_complex64(&from) && is_complex128(&to) {
        true
    } else if (is_float32(&from) || is_float64(&from)) && (is_complex64(&to) || is_complex128(&to)) {
        true
    } else if eq_dtype(&from, &to) {
        true
    } else {
        false
    }
}

fn is_samekind(from: &DType, to: &DType) -> bool {
    let from_int = is_int8(&from) || is_int16(&from) || is_int32(&from) || is_int64(&from);
    let to_int = is_int8(&to) || is_int16(&to) || is_int32(&to) || is_int64(&to);
    let from_float = is_float32(&from) || is_float64(&from);
    let to_float = is_float32(&to) || is_float64(&to);
    let from_complex = is_complex64(&from) || is_complex128(&from);
    let to_complex = is_complex64(&to) || is_complex128(&to);
    (from_int && to_int) || (from_float && to_float) || (from_complex && to_complex) ||
    (from_int && (to_float || to_complex)) ||
    (from_float && to_complex)
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
/* code modified by LLM (iteration 4): Updated helper function calls to pass references */
{
    let result = match casting {
        CastingRule::No => eq_dtype(&from_dtype, &to_dtype),
        CastingRule::Equiv => eq_dtype(&from_dtype, &to_dtype),
        CastingRule::Unrestricted => true,
        CastingRule::Safe => is_safe(&from_dtype, &to_dtype),
        CastingRule::SameKind => is_samekind(&from_dtype, &to_dtype),
    };
    result
}
// </vc-code>

}
fn main() {}