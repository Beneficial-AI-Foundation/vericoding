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
/* helper modified by LLM (iteration 2): classification predicate for integer dtypes */
spec fn is_int_dtype(d: DType) -> bool { d == DType::Int8 || d == DType::Int16 || d == DType::Int32 || d == DType::Int64 }
/* helper modified by LLM (iteration 2): classification predicate for float dtypes */
spec fn is_float_dtype(d: DType) -> bool { d == DType::Float32 || d == DType::Float64 }
/* helper modified by LLM (iteration 2): classification predicate for complex dtypes */
spec fn is_complex_dtype(d: DType) -> bool { d == DType::Complex64 || d == DType::Complex128 }
/* helper modified by LLM (iteration 2): classification predicate for bool dtype */
spec fn is_bool_dtype(d: DType) -> bool { d == DType::Bool }
/* helper modified by LLM (iteration 2): spec predicate for allowed safe casts (subset used in ensures) */
spec fn safe_cast_allowed(from_dtype: DType, to_dtype: DType) -> bool {
    (from_dtype == DType::Int8 && (to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64 || to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
    (from_dtype == DType::Int16 && (to_dtype == DType::Int32 || to_dtype == DType::Int64 || to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
    (from_dtype == DType::Int32 && (to_dtype == DType::Int64 || to_dtype == DType::Float64)) ||
    (from_dtype == DType::Float32 && (to_dtype == DType::Float64 || to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||
    (from_dtype == DType::Float64 && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||
    (from_dtype == DType::Complex64 && to_dtype == DType::Complex128) ||
    (from_dtype == to_dtype)
}
/* helper modified by LLM (iteration 2): spec predicate for SameKind casts (subset used in ensures) */
spec fn same_kind_allowed(from_dtype: DType, to_dtype: DType) -> bool {
    ((is_int_dtype(from_dtype) && is_int_dtype(to_dtype)) ||
     (is_float_dtype(from_dtype) && is_float_dtype(to_dtype)) ||
     (is_complex_dtype(from_dtype) && is_complex_dtype(to_dtype)) ||
     (is_int_dtype(from_dtype) && (is_float_dtype(to_dtype) || is_complex_dtype(to_dtype))) ||
     (is_float_dtype(from_dtype) && is_complex_dtype(to_dtype)))
}
/* helper modified by LLM (iteration 2): executable equality for DType to avoid using external Eq */
fn eq_dtype(a: DType, b: DType) -> bool {
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
    /* code modified by LLM (iteration 2): implemented logic without using == for DType by calling eq_dtype; matches spec cases */
    let result = if eq_dtype(from_dtype, to_dtype) {
        true
    } else {
        match casting {
            CastingRule::Unrestricted => true,
            CastingRule::No => false,
            CastingRule::Equiv => false,
            CastingRule::Safe => {
                match from_dtype {
                    DType::Int8 => match to_dtype {
                        DType::Int16 | DType::Int32 | DType::Int64 | DType::Float32 | DType::Float64 => true,
                        _ => false,
                    },
                    DType::Int16 => match to_dtype {
                        DType::Int32 | DType::Int64 | DType::Float32 | DType::Float64 => true,
                        _ => false,
                    },
                    DType::Int32 => match to_dtype {
                        DType::Int64 | DType::Float64 => true,
                        _ => false,
                    },
                    DType::Int64 => false,
                    DType::Float32 => match to_dtype {
                        DType::Float64 | DType::Complex64 | DType::Complex128 => true,
                        _ => false,
                    },
                    DType::Float64 => match to_dtype {
                        DType::Complex64 | DType::Complex128 => true,
                        _ => false,
                    },
                    DType::Complex64 => match to_dtype {
                        DType::Complex128 => true,
                        _ => false,
                    },
                    DType::Complex128 => false,
                    DType::Bool => false,
                }
            },
            CastingRule::SameKind => {
                match from_dtype {
                    DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 => match to_dtype {
                        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 |
                        DType::Float32 | DType::Float64 | DType::Complex64 | DType::Complex128 => true,
                        _ => false,
                    },
                    DType::Float32 | DType::Float64 => match to_dtype {
                        DType::Float32 | DType::Float64 | DType::Complex64 | DType::Complex128 => true,
                        _ => false,
                    },
                    DType::Complex64 | DType::Complex128 => match to_dtype {
                        DType::Complex64 | DType::Complex128 => true,
                        _ => false,
                    },
                    DType::Bool => false,
                }
            },
        }
    };
    result
}
// </vc-code>

}
fn main() {}