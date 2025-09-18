// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
enum NumpyTypeClass {

    IntegerType,

    FloatingType,

    ComplexType,

    BooleanType,

    ScalarType,

    NumberType,

    InexactType,

    Int8Type,

    Int16Type,

    Int32Type,

    Int64Type,

    UInt8Type,

    UInt16Type,

    UInt32Type,

    UInt64Type,

    Float32Type,

    Float64Type,

    Complex64Type,

    Complex128Type,

    ObjectType,
}

spec fn is_subclass_spec(t: NumpyTypeClass, t_prime: NumpyTypeClass) -> bool {

    if t == t_prime {
        true
    } else {
        match (t, t_prime) {

            (NumpyTypeClass::Int8Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::Int16Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::Int32Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::Int64Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::UInt8Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::UInt16Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::UInt32Type, NumpyTypeClass::IntegerType) => true,
            (NumpyTypeClass::UInt64Type, NumpyTypeClass::IntegerType) => true,

            (NumpyTypeClass::Float32Type, NumpyTypeClass::FloatingType) => true,
            (NumpyTypeClass::Float64Type, NumpyTypeClass::FloatingType) => true,

            (NumpyTypeClass::Complex64Type, NumpyTypeClass::ComplexType) => true,
            (NumpyTypeClass::Complex128Type, NumpyTypeClass::ComplexType) => true,

            (NumpyTypeClass::IntegerType, NumpyTypeClass::NumberType) => true,

            (NumpyTypeClass::FloatingType, NumpyTypeClass::InexactType) => true,
            (NumpyTypeClass::FloatingType, NumpyTypeClass::NumberType) => true,

            (NumpyTypeClass::ComplexType, NumpyTypeClass::InexactType) => true,
            (NumpyTypeClass::ComplexType, NumpyTypeClass::NumberType) => true,

            (NumpyTypeClass::NumberType, NumpyTypeClass::ScalarType) => true,
            (NumpyTypeClass::BooleanType, NumpyTypeClass::ScalarType) => true,
            (NumpyTypeClass::IntegerType, NumpyTypeClass::ScalarType) => true,
            (NumpyTypeClass::FloatingType, NumpyTypeClass::ScalarType) => true,
            (NumpyTypeClass::ComplexType, NumpyTypeClass::ScalarType) => true,
            (NumpyTypeClass::InexactType, NumpyTypeClass::ScalarType) => true,

            _ => false,
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): reflexivity lemma for is_subclass_spec */
proof fn is_subclass_refl(t: NumpyTypeClass) ensures is_subclass_spec(t, t) { }
// </vc-helpers>

// <vc-spec>
fn issubclass_(arg1: NumpyTypeClass, arg2: NumpyTypeClass) -> (result: bool)
    ensures

        result == is_subclass_spec(arg1, arg2),

        (arg1 == arg2) ==> (result == true),

        (arg1 == NumpyTypeClass::Int32Type && arg2 == NumpyTypeClass::IntegerType) ==> (result == true),
        (arg1 == NumpyTypeClass::Float64Type && arg2 == NumpyTypeClass::FloatingType) ==> (result == true),
        (arg1 == NumpyTypeClass::Int32Type && arg2 == NumpyTypeClass::FloatingType) ==> (result == false),

        (arg1 == NumpyTypeClass::Int32Type && arg2 == NumpyTypeClass::NumberType) ==> 
         (is_subclass_spec(NumpyTypeClass::Int32Type, NumpyTypeClass::IntegerType) &&
          is_subclass_spec(NumpyTypeClass::IntegerType, NumpyTypeClass::NumberType)),

        (arg1 == NumpyTypeClass::IntegerType && arg2 == NumpyTypeClass::ScalarType) ==> (result == true),
        (arg1 == NumpyTypeClass::FloatingType && arg2 == NumpyTypeClass::ScalarType) ==> (result == true),
        (arg1 == NumpyTypeClass::ComplexType && arg2 == NumpyTypeClass::ScalarType) ==> (result == true)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement issubclass_ by exhaustive pattern matching to avoid external equality */
    match arg1 {
        NumpyTypeClass::IntegerType => match arg2 {
            NumpyTypeClass::IntegerType => true,
            NumpyTypeClass::NumberType => true,
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::FloatingType => match arg2 {
            NumpyTypeClass::FloatingType => true,
            NumpyTypeClass::InexactType => true,
            NumpyTypeClass::NumberType => true,
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::ComplexType => match arg2 {
            NumpyTypeClass::ComplexType => true,
            NumpyTypeClass::InexactType => true,
            NumpyTypeClass::NumberType => true,
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::BooleanType => match arg2 {
            NumpyTypeClass::BooleanType => true,
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::ScalarType => match arg2 {
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::NumberType => match arg2 {
            NumpyTypeClass::NumberType => true,
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::InexactType => match arg2 {
            NumpyTypeClass::InexactType => true,
            NumpyTypeClass::ScalarType => true,
            _ => false,
        },
        NumpyTypeClass::Int8Type => match arg2 {
            NumpyTypeClass::Int8Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::Int16Type => match arg2 {
            NumpyTypeClass::Int16Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::Int32Type => match arg2 {
            NumpyTypeClass::Int32Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::Int64Type => match arg2 {
            NumpyTypeClass::Int64Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::UInt8Type => match arg2 {
            NumpyTypeClass::UInt8Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::UInt16Type => match arg2 {
            NumpyTypeClass::UInt16Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::UInt32Type => match arg2 {
            NumpyTypeClass::UInt32Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::UInt64Type => match arg2 {
            NumpyTypeClass::UInt64Type => true,
            NumpyTypeClass::IntegerType => true,
            _ => false,
        },
        NumpyTypeClass::Float32Type => match arg2 {
            NumpyTypeClass::Float32Type => true,
            NumpyTypeClass::FloatingType => true,
            _ => false,
        },
        NumpyTypeClass::Float64Type => match arg2 {
            NumpyTypeClass::Float64Type => true,
            NumpyTypeClass::FloatingType => true,
            _ => false,
        },
        NumpyTypeClass::Complex64Type => match arg2 {
            NumpyTypeClass::Complex64Type => true,
            NumpyTypeClass::ComplexType => true,
            _ => false,
        },
        NumpyTypeClass::Complex128Type => match arg2 {
            NumpyTypeClass::Complex128Type => true,
            NumpyTypeClass::ComplexType => true,
            _ => false,
        },
        NumpyTypeClass::ObjectType => match arg2 {
            NumpyTypeClass::ObjectType => true,
            _ => false,
        },
    }
}
// </vc-code>

}
fn main() {}