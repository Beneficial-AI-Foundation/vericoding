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
/* helper modified by LLM (iteration 4): All helper functions remain unchanged from the previous iteration. The previous update focused on introducing these helpers to categorize DTypes, which is still a valid approach for making the main `can_cast` function more readable and maintainable. The current error is within the `vc-code` section, specifically related to how `DType` comparisons are handled, not with the helper functions themselves. Therefore, no modifications are needed in this section. */
spec fn is_int_dtype(dtype: DType) -> bool {
    match dtype {
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 => true,
        _ => false,
    }
}
spec fn is_float_dtype(dtype: DType) -> bool {
    match dtype {
        DType::Float32 | DType::Float64 => true,
        _ => false,
    }
}
spec fn is_complex_dtype(dtype: DType) -> bool {
    match dtype {
        DType::Complex64 | DType::Complex128 => true,
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
/* code modified by LLM (iteration 4): Replaced `matches!(from_dtype, _ if from_dtype == to_dtype)` with direct `from_dtype == to_dtype` to fix the compilation error in Rust. The `matches!` macro with an `_ if` condition is verbose and unnecessary for direct equality checks on enums with `PartialEq` derived. While the previous error message indicated an issue with `eq` being ignored, the Verus macro usually handles `PartialEq` for enums transparently within `fn` blocks when properly defined. By reverting to the more natural `from_dtype == to_dtype`, the compiler can correctly use the derived `PartialEq` implementation. This change simplifies the code and adheres to common Rust practices for enum comparison. */
{
    match casting {
        CastingRule::No => {
            return from_dtype == to_dtype;
        }
        CastingRule::Equiv => {
            return from_dtype == to_dtype;
        }
        CastingRule::Safe => {
            if from_dtype == to_dtype { return true; }

            if from_dtype == DType::Int8 && (to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64) { return true; }
            if from_dtype == DType::Int16 && (to_dtype == DType::Int32 || to_dtype == DType::Int64) { return true; }
            if from_dtype == DType::Int32 && to_dtype == DType::Int64 { return true; }

            if from_dtype == DType::Float32 && to_dtype == DType::Float64 { return true; }

            if (from_dtype == DType::Int8 || from_dtype == DType::Int16) && (to_dtype == DType::Float32 || to_dtype == DType::Float64) { return true; }
            if from_dtype == DType::Int32 && to_dtype == DType::Float64 { return true; }

            if from_dtype == DType::Complex64 && to_dtype == DType::Complex128 { return true; }

            if (from_dtype == DType::Float32 || from_dtype == DType::Float64) && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128) { return true; }

            return false;
        }
        CastingRule::SameKind => {
            if from_dtype == to_dtype { return true; }

            let from_is_int = is_int_dtype(from_dtype);
            let to_is_int = is_int_dtype(to_dtype);
            if from_is_int && to_is_int { return true; }

            let from_is_float = is_float_dtype(from_dtype);
            let to_is_float = is_float_dtype(to_dtype);
            if from_is_float && to_is_float { return true; }

            let from_is_complex = is_complex_dtype(from_dtype);
            let to_is_complex = is_complex_dtype(to_dtype);
            if from_is_complex && to_is_complex { return true; }

            if from_is_int && (to_is_float || to_is_complex) { return true; }
            if from_is_float && to_is_complex { return true; }

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