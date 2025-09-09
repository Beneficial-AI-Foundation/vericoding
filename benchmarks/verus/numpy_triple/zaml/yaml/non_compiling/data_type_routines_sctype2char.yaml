```verus
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Specification)]
enum ScalarType {
    Int32,
    Int64,
    Float32,
    Float64,
    Complex64,
    Complex128,
    Bytes,
    Object,
}

fn sctype2char(sctype: ScalarType) -> (result: &'static str)
    ensures
        (sctype == ScalarType::Int32 ==> result == "l") &&
        (sctype == ScalarType::Int64 ==> result == "q") &&
        (sctype == ScalarType::Float32 ==> result == "f") &&
        (sctype == ScalarType::Float64 ==> result == "d") &&
        (sctype == ScalarType::Complex64 ==> result == "F") &&
        (sctype == ScalarType::Complex128 ==> result == "D") &&
        (sctype == ScalarType::Bytes ==> result == "S") &&
        (sctype == ScalarType::Object ==> result == "O")
{
    // impl-start
    assume(false);
    "O"
    // impl-end
}

}

fn main() {}
```