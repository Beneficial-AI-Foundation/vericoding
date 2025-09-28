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
/* helper modified by LLM (iteration 5): added `proof` keyword to helper functions without `ensures` clauses to fix compilation issues */
pure proof fn is_int_dtype(dtype: DType) -> bool {
    matches!(dtype,
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64)
}
pure proof fn is_float_dtype(dtype: DType) -> bool {
    matches!(dtype,
        DType::Float32 | DType::Float64)
}
pure proof fn is_complex_dtype(dtype: DType) -> bool {
    matches!(dtype,
        DType::Complex64 | DType::Complex128)
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
/* code modified by LLM (iteration 5): fixed `float64` to `complex64` in safe casting and added a check for Bool type */
{
    if from_dtype == to_dtype {
        return true;
    }

    match casting {
        CastingRule::No => {
            return false;
        }
        CastingRule::Equiv => {
            return false;
        }
        CastingRule::Safe => {
            match from_dtype {
                DType::Int8 => {
                    return to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64 || to_dtype == DType::Float32 || to_dtype == DType::Float64;
                }
                DType::Int16 => {
                    return to_dtype == DType::Int32 || to_dtype == DType::Int64 || to_dtype == DType::Float32 || to_dtype == DType::Float64;
                }
                DType::Int32 => {
                    return to_dtype == DType::Int64 || to_dtype == DType::Float64;
                }
                DType::Int64 => {
                    return false;
                }
                DType::Float32 => {
                    return to_dtype == DType::Float64 || to_dtype == DType::Complex64 || to_dtype == DType::Complex128;
                }
                DType::Float64 => {
                    return to_dtype == DType::Complex64 || to_dtype == DType::Complex128; // Changed from Complex128 to Complex64 and Complex128
                }
                DType::Complex64 => {
                    return to_dtype == DType::Complex128;
                }
                DType::Complex128 => {
                    return false;
                }
                DType::Bool => {
                    return false;
                }
            }
        }
        CastingRule::SameKind => {
            let from_is_int_kind = is_int_dtype(from_dtype);
            let to_is_int_kind = is_int_dtype(to_dtype);
            let from_is_float_kind = is_float_dtype(from_dtype);
            let to_is_float_kind = is_float_dtype(to_dtype);
            let from_is_complex_kind = is_complex_dtype(from_dtype);
            let to_is_complex_kind = is_complex_dtype(to_dtype);

            if from_is_int_kind {
                return to_is_int_kind || to_is_float_kind || to_is_complex_kind;
            } else if from_is_float_kind {
                return to_is_float_kind || to_is_complex_kind;
            } else if from_is_complex_kind {
                return to_is_complex_kind;
            } else if from_dtype == DType::Bool {
                return to_dtype == DType::Bool; // Added handling for Bool type
            }
            return false;
        }
        CastingRule::Unrestricted => {
            return true;
        }
    }
}
// </vc-code>

}
fn main() {}