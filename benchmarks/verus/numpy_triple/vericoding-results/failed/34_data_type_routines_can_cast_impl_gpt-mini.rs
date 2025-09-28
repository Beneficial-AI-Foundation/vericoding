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
/* helper modified by LLM (iteration 5): dtype_eq compares two DType values without using == */
fn dtype_eq(a: DType, b: DType) -> bool {
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

/* helper modified by LLM (iteration 5): safe_cast decides if from can safely cast to to */
fn safe_cast(from: DType, to: DType) -> bool {
    match from {
        DType::Int8 => match to { DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 | DType::Float32 | DType::Float64 => true, _ => false },
        DType::Int16 => match to { DType::Int16 | DType::Int32 | DType::Int64 | DType::Float32 | DType::Float64 => true, _ => false },
        DType::Int32 => match to { DType::Int32 | DType::Int64 | DType::Float64 => true, _ => false },
        DType::Int64 => match to { DType::Int64 => true, _ => false },
        DType::Float32 => match to { DType::Float32 | DType::Float64 | DType::Complex64 | DType::Complex128 => true, _ => false },
        DType::Float64 => match to { DType::Float64 | DType::Complex64 | DType::Complex128 => true, _ => false },
        DType::Complex64 => match to { DType::Complex64 | DType::Complex128 => true, _ => false },
        DType::Complex128 => match to { DType::Complex128 => true, _ => false },
        DType::Bool => match to { DType::Bool => true, _ => false },
    }
}

/* helper modified by LLM (iteration 5): samekind_cast checks same-kind or compatible promotions */
fn samekind_cast(from: DType, to: DType) -> bool {
    match from {
        DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 =>
            match to { DType::Int8 | DType::Int16 | DType::Int32 | DType::Int64 | DType::Float32 | DType::Float64 | DType::Complex64 | DType::Complex128 => true, _ => false },
        DType::Float32 | DType::Float64 =>
            match to { DType::Float32 | DType::Float64 | DType::Complex64 | DType::Complex128 => true, _ => false },
        DType::Complex64 | DType::Complex128 =>
            match to { DType::Complex64 | DType::Complex128 => true, _ => false },
        DType::Bool => match to { DType::Bool => true, _ => false },
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
    /* code modified by LLM (iteration 5): implement can_cast using enum equality for No/Equiv and helpers for others */
    let result = match casting {
        CastingRule::No => from_dtype == to_dtype,
        CastingRule::Equiv => from_dtype == to_dtype,
        CastingRule::Unrestricted => true,
        CastingRule::Safe => safe_cast(from_dtype, to_dtype),
        CastingRule::SameKind => samekind_cast(from_dtype, to_dtype),
    };
    result
}

// </vc-code>

}
fn main() {}