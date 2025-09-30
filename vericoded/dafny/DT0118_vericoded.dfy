// <vc-preamble>
/*
 * NumPy dtype specification: Create a data type object.
 * 
 * A numpy array is homogeneous, and contains elements described by a dtype object. 
 * A dtype object can be constructed from different combinations of fundamental numeric types.
 * This specification focuses on creating basic numeric data types like int16, int32, float32, float64.
 * The function maps type specifications to their corresponding DType objects with proper
 * attributes like size, alignment, and signedness.
 */

// Represents a NumPy data type object with its essential attributes
datatype DType = DType(
  // The fundamental numeric type category
  kind: string,
  // The element size in bytes  
  itemsize: nat,
  // The alignment requirement in bytes
  alignment: nat,
  // A descriptive name for the data type
  name: string,
  // Whether the data type is signed (for numeric types)
  signed: bool
)

// Creates a valid data type object with consistent attributes based on the type specification
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_dtype(type_spec: string) returns (dt: DType)
  // Precondition: The type_spec is a valid NumPy type specification
  requires type_spec in {"int8", "int16", "int32", "int64", "float32", "float64", "bool"}
  
  // Postcondition: The resulting DType has consistent attributes that match the specified type
  ensures dt.kind in {"i", "f", "b"}
  ensures dt.itemsize > 0
  ensures dt.alignment > 0 && dt.alignment <= dt.itemsize
  ensures |dt.name| > 0
  
  // Size consistency for specific types
  ensures type_spec == "int8" ==> dt.itemsize == 1 && dt.signed == true && dt.kind == "i"
  ensures type_spec == "int16" ==> dt.itemsize == 2 && dt.signed == true && dt.kind == "i"
  ensures type_spec == "int32" ==> dt.itemsize == 4 && dt.signed == true && dt.kind == "i"
  ensures type_spec == "int64" ==> dt.itemsize == 8 && dt.signed == true && dt.kind == "i"
  ensures type_spec == "float32" ==> dt.itemsize == 4 && dt.kind == "f"
  ensures type_spec == "float64" ==> dt.itemsize == 8 && dt.kind == "f"
  ensures type_spec == "bool" ==> dt.itemsize == 1 && dt.kind == "b"
// </vc-spec>
// <vc-code>
{
  if type_spec == "int8" {
    dt := DType("i", 1, 1, "int8", true);
  } else if type_spec == "int16" {
    dt := DType("i", 2, 2, "int16", true);
  } else if type_spec == "int32" {
    dt := DType("i", 4, 4, "int32", true);
  } else if type_spec == "int64" {
    dt := DType("i", 8, 8, "int64", true);
  } else if type_spec == "float32" {
    dt := DType("f", 4, 4, "float32", false);
  } else if type_spec == "float64" {
    dt := DType("f", 8, 8, "float64", false);
  } else {
    dt := DType("b", 1, 1, "bool", false);
  }
}
// </vc-code>
