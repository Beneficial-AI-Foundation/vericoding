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
/* helper modified by LLM (iteration 5): added spec for Safe casting */ 
fn dt_eq(a: &DType, b: &DType) -> (result: bool)
    ensures
        result == (a == b),
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

/* helper modified by LLM (iteration 5): added spec for Safe casting */ 
fn is_safe_cast(from: &DType, to: &DType) -> (result: bool)
    ensures
        result == (
            (dt_eq(from, &DType::Int8) && (dt_eq(to, &DType::Int16) || dt_eq(to, &DType::Int32) || dt_eq(to, &DType::Int64))) ||
            (dt_eq(from, &DType::Int16) && (dt_eq(to, &DType::Int32) || dt_eq(to, &DType::Int64))) ||
            (dt_eq(from, &DType::Int32) && dt_eq(to, &DType::Int64)) ||
            (dt_eq(from, &DType::Float32) && dt_eq(to, &DType::Float64)) ||
            ((dt_eq(from, &DType::Int8) || dt_eq(from, &DType::Int16)) && (dt_eq(to, &DType::Float32) || dt_eq(to, &DType::Float64))) ||
            (dt_eq(from, &DType::Int32) && dt_eq(to, &DType::Float64)) ||
            (dt_eq(from, &DType::Complex64) && dt_eq(to, &DType::Complex128)) ||
            ((dt_eq(from, &DType::Float32) || dt_eq(from, &DType::Float64)) && (dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))) ||
            dt_eq(from, to)
        ),
{
    (dt_eq(from, &DType::Int8) && (dt_eq(to, &DType::Int16) || dt_eq(to, &DType::Int32) || dt_eq(to, &DType::Int64))) ||
     (dt_eq(from, &DType::Int16) && (dt_eq(to, &DType::Int32) || dt_eq(to, &DType::Int64))) ||
     (dt_eq(from, &DType::Int32) && dt_eq(to, &DType::Int64)) ||
     (dt_eq(from, &DType::Float32) && dt_eq(to, &DType::Float64)) ||
     ((dt_eq(from, &DType::Int8) || dt_eq(from, &DType::Int16)) && (dt_eq(to, &DType::Float32) || dt_eq(to, &DType::Float64))) ||
     (dt_eq(from, &DType::Int32) && dt_eq(to, &DType::Float64)) ||
     (dt_eq(from, &DType::Complex64) && dt_eq(to, &DType::Complex128)) ||
     ((dt_eq(from, &DType::Float32) || dt_eq(from, &DType::Float64)) && (dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))) ||
     dt_eq(from, to)
}

/* helper modified by LLM (iteration 5): added spec for SameKind casting */ 
fn is_same_kind_cast(from: &DType, to: &DType) -> (result: bool)
    ensures
        result == (
            ((dt_eq(from, &DType::Int8) || dt_eq(from, &DType::Int16) || dt_eq(from, &DType::Int32) || dt_eq(from, &DType::Int64)) &&
             (dt_eq(to, &DType::Int8) || dt_eq(to, &DType::Int16) || dt_eq(to, &DType::Int32) || dt_eq(to, &DType::Int64))) ||
            ((dt_eq(from, &DType::Float32) || dt_eq(from, &DType::Float64)) &&
             (dt_eq(to, &DType::Float32) || dt_eq(to, &DType::Float64))) ||
            ((dt_eq(from, &DType::Complex64) || dt_eq(from, &DType::Complex128)) &&
             (dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))) ||
            ((dt_eq(from, &DType::Int8) || dt_eq(from, &DType::Int16) || dt_eq(from, &DType::Int32) || dt_eq(from, &DType::Int64)) &&
             (dt_eq(to, &DType::Float32) || dt_eq(to, &DType::Float64) || dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))) ||
            ((dt_eq(from, &DType::Float32) || dt_eq(from, &DType::Float64)) &&
             (dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128)))
        ),
{
    (((dt_eq(from, &DType::Int8) || dt_eq(from, &DType::Int16) || dt_eq(from, &DType::Int32) || dt_eq(from, &DType::Int64)) && 
      (dt_eq(to, &DType::Int8) || dt_eq(to, &DType::Int16) || dt_eq(to, &DType::Int32) || dt_eq(to, &DType::Int64))) ||
     ((dt_eq(from, &DType::Float32) || dt_eq(from, &DType::Float64)) && 
      (dt_eq(to, &DType::Float32) || dt_eq(to, &DType::Float64))) ||
     ((dt_eq(from, &DType::Complex64) || dt_eq(from, &DType::Complex128)) && 
      (dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))) ||
     ((dt_eq(from, &DType::Int8) || dt_eq(from, &DType::Int16) || dt_eq(from, &DType::Int32) || dt_eq(from, &DType::Int64)) && 
      (dt_eq(to, &DType::Float32) || dt_eq(to, &DType::Float64) || dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))) ||
     ((dt_eq(from, &DType::Float32) || dt_eq(from, &DType::Float64)) && 
      (dt_eq(to, &DType::Complex64) || dt_eq(to, &DType::Complex128))))
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
/* code modified by LLM (iteration 5): implemented the main logic using helper functions */
{
    if dt_eq(&from_dtype, &to_dtype) {
        true
    } else {
        match casting {
            CastingRule::Unrestricted => true,
            CastingRule::Equiv => false,
            CastingRule::No => false,
            CastingRule::Safe => is_safe_cast(&from_dtype, &to_dtype),
            CastingRule::SameKind => is_same_kind_cast(&from_dtype, &to_dtype),
        }
    }
}
// </vc-code>

}
fn main() {}