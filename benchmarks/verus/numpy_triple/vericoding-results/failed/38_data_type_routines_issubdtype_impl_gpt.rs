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
/* helper modified by LLM (iteration 4): removed previous exec equality helper and provided a trivial lemma to keep section valid */
proof fn lemma_dtype_reflexive(a: NumpyDType)
    ensures
        a == a,
{
}

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
    /* code modified by LLM (iteration 4): implement issubdtype via direct pattern matching consistent with spec, avoiding exec/spec mixing */
    let r_else = match (&arg1, &arg2) {
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
    };
    let result = if arg1 == arg2 { true } else { r_else };
    proof {
        if arg1 == arg2 {
            assert(is_sub_dtype_spec(arg1, arg2));
        } else {
            assert(!(arg1 == arg2));
            match (&arg1, &arg2) {
                (NumpyDType::Float32, NumpyDType::Floating(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Float64, NumpyDType::Floating(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Floating(_), NumpyDType::Inexact(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Floating(_), NumpyDType::Number(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Floating(_), NumpyDType::Generic) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }

                (NumpyDType::Int8, NumpyDType::SignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Int16, NumpyDType::SignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Int32, NumpyDType::SignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Int64, NumpyDType::SignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::UInt8, NumpyDType::UnsignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::UInt16, NumpyDType::UnsignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::UInt32, NumpyDType::UnsignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::UInt64, NumpyDType::UnsignedInteger(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::SignedInteger(_), NumpyDType::Integer(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::UnsignedInteger(_), NumpyDType::Integer(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Integer(_), NumpyDType::Number(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Integer(_), NumpyDType::Generic) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }

                (NumpyDType::Str_, NumpyDType::Character(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Bytes_, NumpyDType::Character(_)) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Character(_), NumpyDType::Generic) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }

                (NumpyDType::Bool_, NumpyDType::Generic) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }

                (NumpyDType::Number(_), NumpyDType::Generic) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                (NumpyDType::Inexact(_), NumpyDType::Generic) => { assert(r_else); assert(is_sub_dtype_spec(arg1, arg2)); }
                _ => { assert(!r_else); assert(!is_sub_dtype_spec(arg1, arg2)); }
            }
            assert(r_else == is_sub_dtype_spec(arg1, arg2));
        }
        assert(result == is_sub_dtype_spec(arg1, arg2));
    }
    result
}

// </vc-code>

}
fn main() {}