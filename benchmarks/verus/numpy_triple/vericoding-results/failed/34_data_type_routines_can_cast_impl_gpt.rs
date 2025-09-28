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
/* helper modified by LLM (iteration 5): classification predicate for integer dtypes */
fn is_int_dtype(d: DType) -> bool {
    match d {
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 5): classification predicate for float dtypes */
fn is_float_dtype(d: DType) -> bool {
    match d {
        DType::Float32 | DType::Float64 => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 5): classification predicate for complex dtypes */
fn is_complex_dtype(d: DType) -> bool {
    match d {
        DType::Complex64 | DType::Complex128 => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 5): equality without using trait-based PartialEq; structural match */
fn is_same_dtype(a: DType, b: DType) -> bool {
    match (a, b) {
        (DType::Int8, DType::Int8)
        | (DType::Int16, DType::Int16)
        | (DType::Int32, DType::Int32)
        | (DType::Int64, DType::Int64)
        | (DType::Float32, DType::Float32)
        | (DType::Float64, DType::Float64)
        | (DType::Complex64, DType::Complex64)
        | (DType::Complex128, DType::Complex128)
        | (DType::Bool, DType::Bool) => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 5): safe-casting relation using value dtypes */
fn is_safe_cast(from: DType, to: DType) -> bool {
    match (from, to) {
        // Integer widening and int->float
        (DType::Int8, DType::Int16)
        | (DType::Int8, DType::Int32)
        | (DType::Int8, DType::Int64)
        | (DType::Int8, DType::Float32)
        | (DType::Int8, DType::Float64)
        | (DType::Int16, DType::Int32)
        | (DType::Int16, DType::Int64)
        | (DType::Int16, DType::Float32)
        | (DType::Int16, DType::Float64)
        | (DType::Int32, DType::Int64)
        | (DType::Int32, DType::Float64) => true,

        // Float widening
        (DType::Float32, DType::Float64) => true,

        // Float -> Complex
        (DType::Float32, DType::Complex64)
        | (DType::Float32, DType::Complex128)
        | (DType::Float64, DType::Complex64)
        | (DType::Float64, DType::Complex128) => true,

        // Complex widening
        (DType::Complex64, DType::Complex128) => true,

        _ => false,
    }
}

/* helper modified by LLM (iteration 5): same-kind casting relation using value dtypes */
fn is_samekind_cast(from: DType, to: DType) -> bool {
    (is_int_dtype(from) && (is_int_dtype(to) || is_float_dtype(to) || is_complex_dtype(to))) ||
    (is_float_dtype(from) && (is_float_dtype(to) || is_complex_dtype(to))) ||
    (is_complex_dtype(from) && is_complex_dtype(to))
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
    /* code modified by LLM (iteration 5): avoid trait-based equality; use helper-based structural equality and delegate to helpers */
    if is_same_dtype(from_dtype, to_dtype) {
        return true;
    }
    match casting {
        CastingRule::Unrestricted => true,
        CastingRule::No => false,
        CastingRule::Equiv => false,
        CastingRule::Safe => is_safe_cast(from_dtype, to_dtype),
        CastingRule::SameKind => is_samekind_cast(from_dtype, to_dtype),
    }
}
// </vc-code>

}
fn main() {}