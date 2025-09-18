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
/* helper modified by LLM (iteration 4): Changed helper functions from spec to exec to fix compilation errors. */
fn is_int(d: DType) -> bool {
    d == DType::Int8 || d == DType::Int16 || d == DType::Int32 || d == DType::Int64
}

fn is_float(d: DType) -> bool {
    d == DType::Float32 || d == DType::Float64
}

fn is_complex(d: DType) -> bool {
    d == DType::Complex64 || d == DType::Complex128
}

fn is_safe_promotion(from_dtype: DType, to_dtype: DType) -> bool {
    (from_dtype == DType::Int8 && (to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
    (from_dtype == DType::Int16 && (to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
    (from_dtype == DType::Int32 && to_dtype == DType::Int64) ||
    (from_dtype == DType::Float32 && to_dtype == DType::Float64) ||
    ((from_dtype == DType::Int8 || from_dtype == DType::Int16) && (to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
    (from_dtype == DType::Int32 && to_dtype == DType::Float64) ||
    (from_dtype == DType::Complex64 && to_dtype == DType::Complex128) ||
    ((from_dtype == DType::Float32 || from_dtype == DType::Float64) && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128))
}

fn is_same_kind_promotion(from_dtype: DType, to_dtype: DType) -> bool {
    (is_int(from_dtype) && is_int(to_dtype)) ||
    (is_float(from_dtype) && is_float(to_dtype)) ||
    (is_complex(from_dtype) && is_complex(to_dtype)) ||
    (is_int(from_dtype) && (is_float(to_dtype) || is_complex(to_dtype))) ||
    (is_float(from_dtype) && is_complex(to_dtype))
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
    /* code modified by LLM (iteration 4): Fixed compilation error by calling exec helpers and improved logic. */
    let are_equal = from_dtype == to_dtype;

    match casting {
        CastingRule::Unrestricted => true,
        CastingRule::No => are_equal,
        CastingRule::Equiv => are_equal,
        CastingRule::Safe => are_equal || is_safe_promotion(from_dtype, to_dtype),
        CastingRule::SameKind => are_equal || is_same_kind_promotion(from_dtype, to_dtype),
    }
}
// </vc-code>

}
fn main() {}