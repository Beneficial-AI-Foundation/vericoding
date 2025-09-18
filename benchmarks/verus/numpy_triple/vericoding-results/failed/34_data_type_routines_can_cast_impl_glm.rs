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
/* helper modified by LLM (iteration 5): Replaced == with explicit pattern matching for same-type cases */
fn is_integer_type(dtype: DType) -> bool {
    match dtype {
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 4): Fixed eq usage by using pattern matching instead of == */
fn is_float_type(dtype: DType) -> bool {
    match dtype {
        DType::Float32 | DType::Float64 => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 4): Fixed eq usage by using pattern matching instead of == */
fn is_complex_type(dtype: DType) -> bool {
    match dtype {
        DType::Complex64 | DType::Complex128 => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 5): Replaced == with explicit pattern matching for same-type cases */
fn can_safely_cast(from_dtype: DType, to_dtype: DType) -> bool {
    match (from_dtype, to_dtype) {
        // Same type
        (DType::Int8, DType::Int8) => true,
        (DType::Int16, DType::Int16) => true,
        (DType::Int32, DType::Int32) => true,
        (DType::Int64, DType::Int64) => true,
        (DType::Float32, DType::Float32) => true,
        (DType::Float64, DType::Float64) => true,
        (DType::Complex64, DType::Complex64) => true,
        (DType::Complex128, DType::Complex128) => true,
        (DType::Bool, DType::Bool) => true,

        // Safe casts for integers
        (DType::Int8, DType::Int16) => true,
        (DType::Int8, DType::Int32) => true,
        (DType::Int8, DType::Int64) => true,
        (DType::Int16, DType::Int32) => true,
        (DType::Int16, DType::Int64) => true,
        (DType::Int32, DType::Int64) => true,

        // Safe casts for floats
        (DType::Float32, DType::Float64) => true,

        // Safe casts from integers to floats
        (DType::Int8, DType::Float32) => true,
        (DType::Int8, DType::Float64) => true,
        (DType::Int16, DType::Float32) => true,
        (DType::Int16, DType::Float64) => true,
        (DType::Int32, DType::Float64) => true,

        // Safe casts for complex
        (DType::Complex64, DType::Complex128) => true,

        // Safe casts from floats to complex
        (DType::Float32, DType::Complex64) => true,
        (DType::Float32, DType::Complex128) => true,
        (DType::Float64, DType::Complex64) => true,
        (DType::Float64, DType::Complex128) => true,

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
/* code modified by LLM (iteration 5): Replaced == with explicit pattern matching for same-type cases */
{
    match (from_dtype, to_dtype) {
        // Same type
        (DType::Int8, DType::Int8) => true,
        (DType::Int16, DType::Int16) => true,
        (DType::Int32, DType::Int32) => true,
        (DType::Int64, DType::Int64) => true,
        (DType::Float32, DType::Float32) => true,
        (DType::Float64, DType::Float64) => true,
        (DType::Complex64, DType::Complex64) => true,
        (DType::Complex128, DType::Complex128) => true,
        (DType::Bool, DType::Bool) => true,
        (_, _) => {
            match casting {
                CastingRule::No => false,
                CastingRule::Equiv => false,
                CastingRule::Safe => can_safely_cast(from_dtype, to_dtype),
                CastingRule::SameKind => {
                    (is_integer_type(from_dtype) && (is_integer_type(to_dtype) || is_float_type(to_dtype) || is_complex_type(to_dtype))) ||
                    (is_float_type(from_dtype) && (is_float_type(to_dtype) || is_complex_type(to_dtype))) ||
                    (is_complex_type(from_dtype) && is_complex_type(to_dtype))
                },
                CastingRule::Unrestricted => true,
            }
        }
    }
}
// </vc-code>

}
fn main() {}