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
/* helper modified by LLM (iteration 2): reflexivity of is_subclass_spec */
proof fn lemma_is_subclass_spec_refl(t: NumpyTypeClass)
    ensures
        is_subclass_spec(t, t),
{
    assert(is_subclass_spec(t, t));
}
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
    /* code modified by LLM (iteration 2): avoid using external == by exhaustive match mirroring spec, including equality cases */
    let result: bool = match (arg1, arg2) {
        (NumpyTypeClass::IntegerType, NumpyTypeClass::IntegerType) => true,
        (NumpyTypeClass::FloatingType, NumpyTypeClass::FloatingType) => true,
        (NumpyTypeClass::ComplexType, NumpyTypeClass::ComplexType) => true,
        (NumpyTypeClass::BooleanType, NumpyTypeClass::BooleanType) => true,
        (NumpyTypeClass::ScalarType, NumpyTypeClass::ScalarType) => true,
        (NumpyTypeClass::NumberType, NumpyTypeClass::NumberType) => true,
        (NumpyTypeClass::InexactType, NumpyTypeClass::InexactType) => true,
        (NumpyTypeClass::Int8Type, NumpyTypeClass::Int8Type) => true,
        (NumpyTypeClass::Int16Type, NumpyTypeClass::Int16Type) => true,
        (NumpyTypeClass::Int32Type, NumpyTypeClass::Int32Type) => true,
        (NumpyTypeClass::Int64Type, NumpyTypeClass::Int64Type) => true,
        (NumpyTypeClass::UInt8Type, NumpyTypeClass::UInt8Type) => true,
        (NumpyTypeClass::UInt16Type, NumpyTypeClass::UInt16Type) => true,
        (NumpyTypeClass::UInt32Type, NumpyTypeClass::UInt32Type) => true,
        (NumpyTypeClass::UInt64Type, NumpyTypeClass::UInt64Type) => true,
        (NumpyTypeClass::Float32Type, NumpyTypeClass::Float32Type) => true,
        (NumpyTypeClass::Float64Type, NumpyTypeClass::Float64Type) => true,
        (NumpyTypeClass::Complex64Type, NumpyTypeClass::Complex64Type) => true,
        (NumpyTypeClass::Complex128Type, NumpyTypeClass::Complex128Type) => true,
        (NumpyTypeClass::ObjectType, NumpyTypeClass::ObjectType) => true,

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
    };
    proof {
        assert(result == is_subclass_spec(arg1, arg2));
    }
    result
}
// </vc-code>

}
fn main() {}