// <vc-preamble>
// NumPy scalar data types
datatype NumpyScalarType = 
    | Int32
    | Int64
    | Float32
    | Float64
    | Complex64
    | Complex128
    | Object
    | String
    | Bool

// Option type for NumpyScalarType
datatype NumpyScalarTypeOption = 
    | Some(value: NumpyScalarType)
    | None

// Object representation for type introspection
datatype NumpyObject =
    | IntVal(intValue: int)
    | FloatVal(floatValue: real)
    | ArrayInt(intElements: seq<int>)
    | ArrayFloat(floatElements: seq<real>)
    | ArrayComplex(complexElements: seq<(real, real)>)
    | GenericObj(unit: ())
    | StringVal(stringValue: string)
    | BoolVal(boolValue: bool)

// Helper predicate: Check if object matches given scalar type
ghost predicate MatchesScalarType(obj: NumpyObject, dtype: NumpyScalarType)
{
    match obj 
    case IntVal(_) => dtype == Int64
    case FloatVal(_) => dtype == Float64
    case StringVal(_) => dtype == String
    case BoolVal(_) => dtype == Bool
    case _ => false
}

// Helper predicate: Check if object is an array with given element type
ghost predicate IsArrayWithElementType(obj: NumpyObject, dtype: NumpyScalarType)
{
    match obj
    case ArrayInt(_) => dtype == Int64
    case ArrayFloat(_) => dtype == Float64
    case ArrayComplex(_) => dtype == Complex128
    case _ => false
}

// Helper predicate: Check if object is a generic object
ghost predicate IsGenericObject(obj: NumpyObject)
{
    obj.GenericObj?
}

// Main specification method for obj2sctype
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method obj2sctype(rep: NumpyObject, default: NumpyScalarTypeOption) returns (result: NumpyScalarTypeOption)
    ensures match rep {
        case IntVal(_) => result == Some(Int64)
        case FloatVal(_) => result == Some(Float64)
        case ArrayInt(_) => result == Some(Int64)
        case ArrayFloat(_) => result == Some(Float64)
        case ArrayComplex(_) => result == Some(Complex128)
        case StringVal(_) => result == Some(String)
        case BoolVal(_) => result == Some(Bool)
        case GenericObj(_) => result == default
    }
    ensures match result {
        case Some(dtype) => 
            MatchesScalarType(rep, dtype) || 
            IsArrayWithElementType(rep, dtype) ||
            (IsGenericObject(rep) && result == default)
        case None => IsGenericObject(rep) && default.None?
    }
// </vc-spec>
// <vc-code>
{
  match rep {
    case IntVal(_) => result := Some(Int64);
    case FloatVal(_) => result := Some(Float64);
    case ArrayInt(_) => result := Some(Int64);
    case ArrayFloat(_) => result := Some(Float64);
    case ArrayComplex(_) => result := Some(Complex128);
    case StringVal(_) => result := Some(String);
    case BoolVal(_) => result := Some(Bool);
    case GenericObj(_) => result := default;
  }
}
// </vc-code>
