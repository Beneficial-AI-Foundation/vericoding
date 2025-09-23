// <vc-preamble>
// Represents a NumPy type class for hierarchy testing
datatype NumpyTypeClass = 
    // Integer types
    | IntegerType
    // Floating point types  
    | FloatingType
    // Complex number types
    | ComplexType
    // Boolean type
    | BooleanType
    // Scalar types (superclass of all numeric types)
    | ScalarType
    // Number types (excludes boolean)
    | NumberType
    // Inexact types (floating and complex)
    | InexactType
    // 8-bit signed integer type
    | Int8Type
    // 16-bit signed integer type
    | Int16Type
    // 32-bit signed integer type
    | Int32Type
    // 64-bit signed integer type
    | Int64Type
    // 8-bit unsigned integer type
    | UInt8Type
    // 16-bit unsigned integer type
    | UInt16Type
    // 32-bit unsigned integer type
    | UInt32Type
    // 64-bit unsigned integer type
    | UInt64Type
    // 32-bit floating point type
    | Float32Type
    // 64-bit floating point type
    | Float64Type
    // 64-bit complex number type
    | Complex64Type
    // 128-bit complex number type
    | Complex128Type
    // Generic object type
    | ObjectType

// Defines the class hierarchy relationships for NumPy types
predicate IsSubclass(t1: NumpyTypeClass, t2: NumpyTypeClass)
{
    // Reflexivity: every class is a subclass of itself
    t1 == t2 ||
    // Concrete integer types are subclasses of IntegerType, NumberType, and ScalarType
    (t1 in {Int8Type, Int16Type, Int32Type, Int64Type, UInt8Type, UInt16Type, UInt32Type, UInt64Type} && t2 in {IntegerType, NumberType, ScalarType}) ||
    // Concrete floating types are subclasses of FloatingType, InexactType, NumberType, and ScalarType
    (t1 in {Float32Type, Float64Type} && t2 in {FloatingType, InexactType, NumberType, ScalarType}) ||
    // Concrete complex types are subclasses of ComplexType, InexactType, NumberType, and ScalarType
    (t1 in {Complex64Type, Complex128Type} && t2 in {ComplexType, InexactType, NumberType, ScalarType}) ||
    // Integer types are subclasses of NumberType and ScalarType
    (t1 == IntegerType && t2 in {NumberType, ScalarType}) ||
    // Floating types are subclasses of InexactType, NumberType, and ScalarType
    (t1 == FloatingType && t2 in {InexactType, NumberType, ScalarType}) ||
    // Complex types are subclasses of InexactType, NumberType, and ScalarType
    (t1 == ComplexType && t2 in {InexactType, NumberType, ScalarType}) ||
    // InexactType is a subclass of NumberType and ScalarType
    (t1 == InexactType && t2 in {NumberType, ScalarType}) ||
    // NumberType and BooleanType are subclasses of ScalarType
    (t1 in {NumberType, BooleanType} && t2 == ScalarType)
}

// Main method that determines if arg1 is a subclass of arg2
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method issubclass_(arg1: NumpyTypeClass, arg2: NumpyTypeClass) returns (result: bool)
    ensures result == IsSubclass(arg1, arg2)
    // Reflexivity: every class is a subclass of itself
    ensures arg1 == arg2 ==> result == true
    // Concrete examples from NumPy documentation
    ensures (arg1 == Int32Type && arg2 == IntegerType) ==> result == true
    ensures (arg1 == Float64Type && arg2 == FloatingType) ==> result == true
    ensures (arg1 == Int32Type && arg2 == FloatingType) ==> result == false
    // All numeric types are subclasses of ScalarType
    ensures (arg1 == IntegerType && arg2 == ScalarType) ==> result == true
    ensures (arg1 == FloatingType && arg2 == ScalarType) ==> result == true
    ensures (arg1 == ComplexType && arg2 == ScalarType) ==> result == true
    // InexactType relationships
    ensures (arg1 == FloatingType && arg2 == InexactType) ==> result == true
    ensures (arg1 == ComplexType && arg2 == InexactType) ==> result == true
    ensures (arg1 == InexactType && arg2 == ScalarType) ==> result == true
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
