// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Scalar data type enumeration for numpy types */
pub enum ScalarType {
    /* 32-bit signed integer */
    Int32,
    /* 64-bit signed integer */
    Int64,
    /* 32-bit floating point */
    Float32,
    /* 64-bit floating point */
    Float64,
    /* 64-bit complex number */
    Complex64,
    /* 128-bit complex number */
    Complex128,
    /* Byte string */
    Bytes,
    /* Generic object */
    Object,
}
// </vc-preamble>

// <vc-helpers>
fn code_of(sctype: ScalarType) -> (result: &'static str)
    ensures
        (sctype == ScalarType::Int32) ==> (result == "l"),
        (sctype == ScalarType::Int64) ==> (result == "q"),
        (sctype == ScalarType::Float32) ==> (result == "f"),
        (sctype == ScalarType::Float64) ==> (result == "d"),
        (sctype == ScalarType::Complex64) ==> (result == "F"),
        (sctype == ScalarType::Complex128) ==> (result == "D"),
        (sctype == ScalarType::Bytes) ==> (result == "S"),
        (sctype == ScalarType::Object) ==> (result == "O"),
{
    match sctype {
        ScalarType::Int32 => "l",
        ScalarType::Int64 => "q",
        ScalarType::Float32 => "f",
        ScalarType::Float64 => "d",
        ScalarType::Complex64 => "F",
        ScalarType::Complex128 => "D",
        ScalarType::Bytes => "S",
        ScalarType::Object => "O",
    }
}
// </vc-helpers>

// <vc-spec>
fn sctype2char(sctype: ScalarType) -> (result: &'static str)
    ensures
        (sctype == ScalarType::Int32) ==> (result == "l"),
        (sctype == ScalarType::Int64) ==> (result == "q"),
        (sctype == ScalarType::Float32) ==> (result == "f"),
        (sctype == ScalarType::Float64) ==> (result == "d"),
        (sctype == ScalarType::Complex64) ==> (result == "F"),
        (sctype == ScalarType::Complex128) ==> (result == "D"),
        (sctype == ScalarType::Bytes) ==> (result == "S"),
        (sctype == ScalarType::Object) ==> (result == "O")
// </vc-spec>
// <vc-code>
{
    let r = code_of(sctype);
    r
}
// </vc-code>


}
fn main() {}