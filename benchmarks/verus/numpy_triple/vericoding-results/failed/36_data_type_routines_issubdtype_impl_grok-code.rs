// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NumpyDType {

    Generic,

    Inexact(Box<NumpyDType>),

    Floating(Box<NumpyDType>),

    Float32,

    Float64,

    Number(Box<NumpyDType>),

    Integer(Box<NumpyDType>),

    SignedInteger(Box<NumpyDType>),

    Int8,

    Int16,

    Int32,

    Int64,

    UnsignedInteger(Box<NumpyDType>),

    UInt8,

    UInt16,

    UInt32,

    UInt64,

    Character(Box<NumpyDType>),

    Bytes_,

    Str_,

    Bool_,
}

spec fn is_sub_dtype_spec(dtype1: NumpyDType, dtype2: NumpyDType) -> bool {
    if dtype1 == dtype2 {
        true
    } else {
        match (dtype1, dtype2) {

            (NumpyDType::Float32, NumpyDType::Floating(_)) => true,
            (NumpyDType::Float64, NumpyDType::Floating(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Inexact(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Number(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Generic) => true,

            (NumpyDType::Int8, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int16, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int32, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int64, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::UInt8, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt16, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt32, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt64, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::SignedInteger(_), NumpyDType::Integer(_)) => true,
            (NumpyDType::UnsignedInteger(_), NumpyDType::Integer(_)) => true,
            (NumpyDType::Integer(_), NumpyDType::Number(_)) => true,
            (NumpyDType::Integer(_), NumpyDType::Generic) => true,

            (NumpyDType::Str_, NumpyDType::Character(_)) => true,
            (NumpyDType::Bytes_, NumpyDType::Character(_)) => true,
            (NumpyDType::Character(_), NumpyDType::Generic) => true,

            (NumpyDType::Bool_, NumpyDType::Generic) => true,

            (NumpyDType::Number(_), NumpyDType::Generic) => true,
            (NumpyDType::Inexact(_), NumpyDType::Generic) => true,
            _ => false,
        }
    }
}
// </vc-preamble>

// <vc-helpers>
impl std::cmp::PartialEq for NumpyDType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (NumpyDType::Generic, NumpyDType::Generic) => true,
            (NumpyDType::Inexact(ref a), NumpyDType::Inexact(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::Floating(ref a), NumpyDType::Floating(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::Float32, NumpyDType::Float32) => true,
            (NumpyDType::Float64, NumpyDType::Float64) => true,
            (NumpyDType::Number(ref a), NumpyDType::Number(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::Integer(ref a), NumpyDType::Integer(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::SignedInteger(ref a), NumpyDType::SignedInteger(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::Int8, NumpyDType::Int8) => true,
            (NumpyDType::Int16, NumpyDType::Int16) => true,
            (NumpyDType::Int32, NumpyDType::Int32) => true,
            (NumpyDType::Int64, NumpyDType::Int64) => true,
            (NumpyDType::UnsignedInteger(ref a), NumpyDType::UnsignedInteger(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::UInt8, NumpyDType::UInt8) => true,
            (NumpyDType::UInt16, NumpyDType::UInt16) => true,
            (NumpyDType::UInt32, NumpyDType::UInt32) => true,
            (NumpyDType::UInt64, NumpyDType::UInt64) => true,
            (NumpyDType::Character(ref a), NumpyDType::Character(ref b)) => a.as_ref().eq(b.as_ref()),
            (NumpyDType::Bytes_, NumpyDType::Bytes_) => true,
            (NumpyDType::Str_, NumpyDType::Str_) => true,
            (NumpyDType::Bool_, NumpyDType::Bool_) => true,
            _ => false,
        }
    }
}

fn helper_is_sub(dtype1: NumpyDType, dtype2: NumpyDType) -> bool {
    if dtype1 == dtype2 {
        true
    } else {
        match (dtype1, dtype2) {
            (NumpyDType::Float32, NumpyDType::Floating(_)) => true,
            (NumpyDType::Float64, NumpyDType::Floating(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Inexact(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Number(_)) => true,
            (NumpyDType::Floating(_), NumpyDType::Generic) => true,
            (NumpyDType::Int8, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int16, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int32, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::Int64, NumpyDType::SignedInteger(_)) => true,
            (NumpyDType::UInt8, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt16, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt32, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::UInt64, NumpyDType::UnsignedInteger(_)) => true,
            (NumpyDType::SignedInteger(_), NumpyDType::Integer(_)) => true,
            (NumpyDType::UnsignedInteger(_), NumpyDType::Integer(_)) => true,
            (NumpyDType::Integer(_), NumpyDType::Number(_)) => true,
            (NumpyDType::Integer(_), NumpyDType::Generic) => true,
            (NumpyDType::Str_, NumpyDType::Character(_)) => true,
            (NumpyDType::Bytes_, NumpyDType::Character(_)) => true,
            (NumpyDType::Character(_), NumpyDType::Generic) => true,
            (NumpyDType::Bool_, NumpyDType::Generic) => true,
            (NumpyDType::Number(_), NumpyDType::Generic) => true,
            (NumpyDType::Inexact(_), NumpyDType::Generic) => true,
            _ => false,
        }
    }
}
/* helper modified by LLM (iteration 5): fixed PartialEq impl for recursive enum to enable equality on executable code without verification bypasses */
// </vc-helpers>

// <vc-spec>
fn issubdtype(arg1: NumpyDType, arg2: NumpyDType) -> (result: bool)
    ensures 
        result == is_sub_dtype_spec(arg1, arg2) &&

        (arg1 == arg2 ==> result == true) &&

        (arg2 == NumpyDType::Generic ==> result == true) &&

        (arg1 == NumpyDType::Float32 && matches!(arg2, NumpyDType::Floating(_)) ==> result == true) &&
        (arg1 == NumpyDType::Float64 && matches!(arg2, NumpyDType::Floating(_)) ==> result == true) &&
        (arg1 == NumpyDType::Int32 && matches!(arg2, NumpyDType::SignedInteger(_)) ==> result == true) &&
        (arg1 == NumpyDType::UInt32 && matches!(arg2, NumpyDType::UnsignedInteger(_)) ==> result == true) &&

        (arg1 == NumpyDType::Float32 && arg2 == NumpyDType::Float64 ==> result == false) &&
        (arg1 == NumpyDType::Float64 && arg2 == NumpyDType::Float32 ==> result == false) &&
        (arg1 == NumpyDType::Int32 && matches!(arg2, NumpyDType::Floating(_)) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call the executable helper function with recursive equality support */
    helper_is_sub(arg1, arg2)
}
// </vc-code>

}
fn main() {}