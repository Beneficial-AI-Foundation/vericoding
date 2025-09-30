// <vc-preamble>
// Scalar data type enumeration for numpy types
datatype ScalarType = 
  | Int32      // 32-bit signed integer
  | Int64      // 64-bit signed integer  
  | Float32    // 32-bit floating point
  | Float64    // 64-bit floating point
  | Complex64  // 64-bit complex number
  | Complex128 // 128-bit complex number
  | Bytes      // Byte string
  | Object     // Generic object

// Return the string representation of a scalar dtype
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sctype2char(sctype: ScalarType) returns (result: string)
  ensures sctype == ScalarType.Int32 ==> result == "l"
  ensures sctype == ScalarType.Int64 ==> result == "q"
  ensures sctype == ScalarType.Float32 ==> result == "f"
  ensures sctype == ScalarType.Float64 ==> result == "d"
  ensures sctype == ScalarType.Complex64 ==> result == "F"
  ensures sctype == ScalarType.Complex128 ==> result == "D"
  ensures sctype == ScalarType.Bytes ==> result == "S"
  ensures sctype == ScalarType.Object ==> result == "O"
// </vc-spec>
// <vc-code>
{
  match sctype {
    case Int32 => result := "l";
    case Int64 => result := "q";
    case Float32 => result := "f";
    case Float64 => result := "d";
    case Complex64 => result := "F";
    case Complex128 => result := "D";
    case Bytes => result := "S";
    case Object => result := "O";
  }
}
// </vc-code>
