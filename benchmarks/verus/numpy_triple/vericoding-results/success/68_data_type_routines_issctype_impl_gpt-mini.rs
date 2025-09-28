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
/* helper modified by LLM (iteration 2): simplified proof without proof blocks */
proof fn is_scalar_type_equiv(rep: DataType)
    ensures is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)
{
    match rep {
        DataType::ScalarInt => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::ScalarFloat => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::ScalarComplex => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::ScalarBool => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::ScalarString => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::ArrayType => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::CompositeType => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
        DataType::UnknownType => { assert(is_scalar_type(rep) == (rep == DataType::ScalarInt || rep == DataType::ScalarFloat || rep == DataType::ScalarComplex || rep == DataType::ScalarBool || rep == DataType::ScalarString)); },
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
/* code modified by LLM (iteration 2): return boolean matching DataType variants */
    match rep {
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

// </vc-code>

}
fn main() {}