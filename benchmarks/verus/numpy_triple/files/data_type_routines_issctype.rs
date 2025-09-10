/* Determines whether the given object represents a scalar data-type */

use vstd::prelude::*;

verus! {

/* Represents different kinds of data types that can be tested */
enum DataType {
    /* Scalar integer type */
    ScalarInt,
    /* Scalar floating point type */
    ScalarFloat,
    /* Scalar complex number type */
    ScalarComplex,
    /* Scalar boolean type */
    ScalarBool,
    /* Scalar string type */
    ScalarString,
    /* Array type */
    ArrayType,
    /* Composite type */
    CompositeType,
    /* Unknown type */
    UnknownType,
}

/* Helper function to check if a DataType is a scalar type */
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
fn issctype(rep: DataType) -> (result: bool)
    ensures result == (rep == DataType::ScalarInt || 
                      rep == DataType::ScalarFloat || 
                      rep == DataType::ScalarComplex || 
                      rep == DataType::ScalarBool || 
                      rep == DataType::ScalarString)
{
    // impl-start
    assume(false);
    false
    // impl-end
}
}
fn main() {}