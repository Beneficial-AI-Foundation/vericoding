// <vc-preamble>
// Represents different kinds of data types that can be tested
datatype DataType = 
  | ScalarInt       // Scalar integer type
  | ScalarFloat     // Scalar floating point type  
  | ScalarComplex   // Scalar complex number type
  | ScalarBool      // Scalar boolean type
  | ScalarString    // Scalar string type
  | ArrayType       // Array type
  | CompositeType   // Composite type
  | UnknownType     // Unknown type

// Predicate to determine if a DataType represents a scalar type
ghost predicate IsScalarDataType(dt: DataType)
{
  dt == ScalarInt || dt == ScalarFloat || dt == ScalarComplex || 
  dt == ScalarBool || dt == ScalarString
}

/**
 * Determines whether the given object represents a scalar data-type.
 * Returns true if and only if the input represents a scalar data type.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsScType(rep: DataType) returns (result: bool)
  ensures result <==> IsScalarDataType(rep)
  ensures result <==> (rep == ScalarInt || rep == ScalarFloat || 
                      rep == ScalarComplex || rep == ScalarBool || 
                      rep == ScalarString)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
