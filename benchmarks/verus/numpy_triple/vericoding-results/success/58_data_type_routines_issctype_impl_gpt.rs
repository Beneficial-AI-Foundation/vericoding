// <vc-preamble>
use vstd::prelude::*;

verus! {

enum DataType {

    ScalarInt,

    ScalarFloat,

    ScalarComplex,

    ScalarBool,

    ScalarString,

    ArrayType,

    CompositeType,

    UnknownType,
}

spec fn is_scalar_type(dt: DataType) -> bool {
    match dt {
        DataType::ScalarInt => true,
        DataType::ScalarFloat => true,
        DataType::ScalarComplex => true,
        DataType::ScalarBool => true,
        DataType::ScalarString => true,
        DataType::ArrayType => false,
        DataType::CompositeType => false,
        DataType::UnknownType => false,
    }
}
// </vc-preamble>

// <vc-helpers>
fn is_scalar_exec(dt: DataType) -> (b: bool)
    ensures b == (dt == DataType::ScalarInt ||
                  dt == DataType::ScalarFloat ||
                  dt == DataType::ScalarComplex ||
                  dt == DataType::ScalarBool ||
                  dt == DataType::ScalarString)
{
    match dt {
        DataType::ScalarInt => true,
        DataType::ScalarFloat => true,
        DataType::ScalarComplex => true,
        DataType::ScalarBool => true,
        DataType::ScalarString => true,
        _ => false,
    }
}
// </vc-helpers>

// <vc-spec>
fn issctype(rep: DataType) -> (result: bool)
    ensures result == (rep == DataType::ScalarInt || 
                      rep == DataType::ScalarFloat || 
                      rep == DataType::ScalarComplex || 
                      rep == DataType::ScalarBool || 
                      rep == DataType::ScalarString)
// </vc-spec>
// <vc-code>
{
    let result = is_scalar_exec(rep);
    result
}
// </vc-code>

}
fn main() {}