// <vc-preamble>
// Method to return a description for a given data type code
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method typename(typeChar: string) returns (result: string)
  ensures 
    // Known type code mappings from NumPy documentation
    (typeChar == "S1" ==> result == "character") &&
    (typeChar == "?" ==> result == "bool") &&
    (typeChar == "B" ==> result == "unsigned char") &&
    (typeChar == "D" ==> result == "complex double precision") &&
    (typeChar == "G" ==> result == "complex long double precision") &&
    (typeChar == "F" ==> result == "complex single precision") &&
    (typeChar == "I" ==> result == "unsigned integer") &&
    (typeChar == "H" ==> result == "unsigned short") &&
    (typeChar == "L" ==> result == "unsigned long integer") &&
    (typeChar == "O" ==> result == "object") &&
    (typeChar == "Q" ==> result == "unsigned long long integer") &&
    (typeChar == "S" ==> result == "character") &&
    (typeChar == "U" ==> result == "unicode") &&
    (typeChar == "V" ==> result == "void") &&
    (typeChar == "b" ==> result == "signed char") &&
    (typeChar == "d" ==> result == "double precision") &&
    (typeChar == "g" ==> result == "long precision") &&
    (typeChar == "f" ==> result == "single precision") &&
    (typeChar == "i" ==> result == "integer") &&
    (typeChar == "h" ==> result == "short") &&
    (typeChar == "l" ==> result == "long integer") &&
    (typeChar == "q" ==> result == "long long integer")
  ensures 
    // For unknown type codes, return either "unknown type" or the original char
    (typeChar !in {"S1", "?", "B", "D", "G", "F", "I", "H", "L", "O", "Q", 
               "S", "U", "V", "b", "d", "g", "f", "i", "h", "l", "q"} ==> 
     (result == "unknown type" || result == typeChar))
// </vc-spec>
// <vc-code>
{
  if typeChar == "S1" {
    result := "character";
  } else if typeChar == "?" {
    result := "bool";
  } else if typeChar == "B" {
    result := "unsigned char";
  } else if typeChar == "D" {
    result := "complex double precision";
  } else if typeChar == "G" {
    result := "complex long double precision";
  } else if typeChar == "F" {
    result := "complex single precision";
  } else if typeChar == "I" {
    result := "unsigned integer";
  } else if typeChar == "H" {
    result := "unsigned short";
  } else if typeChar == "L" {
    result := "unsigned long integer";
  } else if typeChar == "O" {
    result := "object";
  } else if typeChar == "Q" {
    result := "unsigned long long integer";
  } else if typeChar == "S" {
    result := "character";
  } else if typeChar == "U" {
    result := "unicode";
  } else if typeChar == "V" {
    result := "void";
  } else if typeChar == "b" {
    result := "signed char";
  } else if typeChar == "d" {
    result := "double precision";
  } else if typeChar == "g" {
    result := "long precision";
  } else if typeChar == "f" {
    result := "single precision";
  } else if typeChar == "i" {
    result := "integer";
  } else if typeChar == "h" {
    result := "short";
  } else if typeChar == "l" {
    result := "long integer";
  } else if typeChar == "q" {
    result := "long long integer";
  } else {
    result := "unknown type";
  }
}
// </vc-code>
