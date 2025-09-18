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
/* helper modified by LLM (iteration 5): predicate for integer types */
spec fn is_int(d: DType) -> bool { match d { DType::Int8 => true, DType::Int16 => true, DType::Int32 => true, DType::Int64 => true, _ => false } }
/* helper modified by LLM (iteration 5): predicate for float types */
spec fn is_float(d: DType) -> bool { match d { DType::Float32 => true, DType::Float64 => true, _ => false } }
/* helper modified by LLM (iteration 5): predicate for complex types */
spec fn is_complex(d: DType) -> bool { match d { DType::Complex64 => true, DType::Complex128 => true, _ => false } }
/* helper modified by LLM (iteration 5): equality check for DType */
spec fn dtype_eq(a: DType, b: DType) -> bool { a == b }
/* helper modified by LLM (iteration 5): safe cast relation using pattern matching */
spec fn safe_cast(from: DType, to: DType) -> bool { match (from,to) { (DType::Int8, DType::Int16) | (DType::Int8, DType::Int32) | (DType::Int8, DType::Int64) | (DType::Int16, DType::Int32) | (DType::Int16, DType::Int64) | (DType::Int32, DType::Int64) | (DType::Float32, DType::Float64) | (DType::Int8, DType::Float32) | (DType::Int8, DType::Float64) | (DType::Int16, DType::Float32) | (DType::Int16, DType::Float64) | (DType::Int32, DType::Float64) | (DType::Complex64, DType::Complex128) | (DType::Float32, DType::Complex64) | (DType::Float32, DType::Complex128) | (DType::Float64, DType::Complex64) | (DType::Float64, DType::Complex128) | (DType::Int8, DType::Int8) | (DType::Int16, DType::Int16) | (DType::Int32, DType::Int32) | (DType::Int64, DType::Int64) | (DType::Float32, DType::Float32) | (DType::Float64, DType::Float64) | (DType::Complex64, DType::Complex64) | (DType::Complex128, DType::Complex128) | (DType::Bool, DType::Bool) => true, _ => false } }
/* helper modified by LLM (iteration 5): same-kind cast relation using pattern matching */
spec fn same_kind_cast(from: DType, to: DType) -> bool { match (from,to) { (DType::Int8, DType::Int8) | (DType::Int8, DType::Int16) | (DType::Int8, DType::Int32) | (DType::Int8, DType::Int64) | (DType::Int16, DType::Int8) | (DType::Int16, DType::Int16) | (DType::Int16, DType::Int32) | (DType::Int16, DType::Int64) | (DType::Int32, DType::Int8) | (DType::Int32, DType::Int16) | (DType::Int32, DType::Int32) | (DType::Int32, DType::Int64) | (DType::Int64, DType::Int8) | (DType::Int64, DType::Int16) | (DType::Int64, DType::Int32) | (DType::Int64, DType::Int64) | (DType::Float32, DType::Float32) | (DType::Float32, DType::Float64) | (DType::Float64, DType::Float32) | (DType::Float64, DType::Float64) | (DType::Complex64, DType::Complex64) | (DType::Complex64, DType::Complex128) | (DType::Complex128, DType::Complex64) | (DType::Complex128, DType::Complex128) | (DType::Int8, DType::Float32) | (DType::Int8, DType::Float64) | (DType::Int8, DType::Complex64) | (DType::Int8, DType::Complex128) | (DType::Int16, DType::Float32) | (DType::Int16, DType::Float64) | (DType::Int16, DType::Complex64) | (DType::Int16, DType::Complex128) | (DType::Int32, DType::Float32) | (DType::Int32, DType::Float64) | (DType::Int32, DType::Complex64) | (DType::Int32, DType::Complex128) | (DType::Int64, DType::Float32) | (DType::Int64, DType::Float64) | (DType::Int64, DType::Complex64) | (DType::Int64, DType::Complex128) | (DType::Float32, DType::Complex64) | (DType::Float32, DType::Complex128) | (DType::Float64, DType::Complex64) | (DType::Float64, DType::Complex128) | (DType::Bool, DType::Bool) => true, _ => false } }
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
    /* code modified by LLM (iteration 5): implement can_cast without spec-only helpers */
    match casting {
        CastingRule::Unrestricted => true,
        CastingRule::No | CastingRule::Equiv => from_dtype == to_dtype,
        CastingRule::Safe => {
            (
                (from_dtype == DType::Int8 && (to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
                (from_dtype == DType::Int16 && (to_dtype == DType::Int32 || to_dtype == DType::Int64)) ||
                (from_dtype == DType::Int32 && to_dtype == DType::Int64) ||
                (from_dtype == DType::Float32 && to_dtype == DType::Float64) ||
                ((from_dtype == DType::Int8 || from_dtype == DType::Int16) && (to_dtype == DType::Float32 || to_dtype == DType::Float64)) ||
                (from_dtype == DType::Int32 && to_dtype == DType::Float64) ||
                (from_dtype == DType::Complex64 && to_dtype == DType::Complex128) ||
                ((from_dtype == DType::Float32 || from_dtype == DType::Float64) && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128)) ||
                (from_dtype == to_dtype)
            )
        },
        CastingRule::SameKind => {
            (
                (((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) &&
                  (to_dtype == DType::Int8 || to_dtype == DType::Int16 || to_dtype == DType::Int32 || to_dtype == DType::Int64))) ||
                (((from_dtype == DType::Float32 || from_dtype == DType::Float64) && (to_dtype == DType::Float32 || to_dtype == DType::Float64))) ||
                (((from_dtype == DType::Complex64 || from_dtype == DType::Complex128) && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128))) ||
                (((from_dtype == DType::Int8 || from_dtype == DType::Int16 || from_dtype == DType::Int32 || from_dtype == DType::Int64) &&
                  (to_dtype == DType::Float32 || to_dtype == DType::Float64 || to_dtype == DType::Complex64 || to_dtype == DType::Complex128))) ||
                (((from_dtype == DType::Float32 || from_dtype == DType::Float64) && (to_dtype == DType::Complex64 || to_dtype == DType::Complex128)))
            )
        },
    }
}
// </vc-code>

}
fn main() {}