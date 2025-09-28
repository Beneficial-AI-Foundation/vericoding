// <vc-preamble>
// Method to return a description for a given data type code
// </vc-preamble>

// <vc-helpers>
function mapType(c: string): string {
  if c == "S1" then "character"
  else if c == "?" then "bool"
  else if c == "B" then "unsigned char"
  else if c == "D" then "complex double precision"
  else if c == "G" then "complex long double precision"
  else if c == "F" then "complex single precision"
  else if c == "I" then "unsigned integer"
  else if c == "H" then "unsigned short"
  else if c == "L" then "unsigned long integer"
  else if c == "O" then "object"
  else if c == "Q" then "unsigned long long integer"
  else if c == "S" then "character"
  else if c == "U" then "unicode"
  else if c == "V" then "void"
  else if c == "b" then "signed char"
  else if c == "d" then "double precision"
  else if c == "g" then "long precision"
  else if c == "f" then "single precision"
  else if c == "i" then "integer"
  else if c == "h" then "short"
  else if c == "l" then "long integer"
  else if c == "q" then "long long integer"
  else "unknown type"
}
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
  result := mapType(typeChar);
}
// </vc-code>
