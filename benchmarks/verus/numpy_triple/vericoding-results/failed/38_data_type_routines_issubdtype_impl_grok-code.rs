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
fn is_dtype_equal_exec(dtype1: &NumpyDType, dtype2: &NumpyDType) -> (b: bool)
    ensures
        b == (dtype1 == dtype2),
    decreases dtype1, dtype2,
{
    match (dtype1, dtype2) {
        (&NumpyDType::Generic, &NumpyDType::Generic) => true,
        (&NumpyDType::Inexact(ref d1), &NumpyDType::Inexact(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::Floating(ref d1), &NumpyDType::Floating(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::Float32, &NumpyDType::Float32) => true,
        (&NumpyDType::Float64, &NumpyDType::Float64) => true,
        (&NumpyDType::Number(ref d1), &NumpyDType::Number(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::Integer(ref d1), &NumpyDType::Integer(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::SignedInteger(ref d1), &NumpyDType::SignedInteger(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::Int8, &NumpyDType::Int8) => true,
        (&NumpyDType::Int16, &NumpyDType::Int16) => true,
        (&NumpyDType::Int32, &NumpyDType::Int32) => true,
        (&NumpyDType::Int64, &NumpyDType::Int64) => true,
        (&NumpyDType::UnsignedInteger(ref d1), &NumpyDType::UnsignedInteger(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::UInt8, &NumpyDType::UInt8) => true,
        (&NumpyDType::UInt16, &NumpyDType::UInt16) => true,
        (&NumpyDType::UInt32, &NumpyDType::UInt32) => true,
        (&NumpyDType::UInt64, &NumpyDType::UInt64) => true,
        (&NumpyDType::Character(ref d1), &NumpyDType::Character(ref d2)) => is_dtype_equal_exec(d1, d2),
        (&NumpyDType::Bytes_, &NumpyDType::Bytes_) => true,
        (&NumpyDType::Str_, &NumpyDType::Str_) => true,
        (&NumpyDType::Bool_, &NumpyDType::Bool_) => true,
        _ => false,
    }
}

/* helper modified by LLM (iteration 5): changed to take references to avoid ownership issues */
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
    /* code modified by LLM (iteration 5): updated helper call to use references */
    if is_dtype_equal_exec(&arg1, &arg2) {
        true
    } else {
        match (arg1, arg2) {
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
// </vc-code>

}
fn main() {}