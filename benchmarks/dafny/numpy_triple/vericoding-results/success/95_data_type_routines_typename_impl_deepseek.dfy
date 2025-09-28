// <vc-preamble>
// Method to return a description for a given data type code
// </vc-preamble>

// <vc-helpers>
function IsKnownTypeChar(typeChar: string): bool {
  typeChar in {"S1", "?", "B", "D", "G", "F", "I", "H", "L", "O", "Q", "S", "U", "V", "b", "d", "g", "f", "i", "h", "l", "q"}
}

function MapTypeCharToName(typeChar: string): string
  requires IsKnownTypeChar(typeChar)
{
  if typeChar == "S1" then "character"
  else if typeChar == "?" then "bool"
  else if typeChar == "B" then "unsigned char"
  else if typeChar == "D" then "complex double precision"
  else if typeChar == "G" then "complex long double precision"
  else if typeChar == "F" then "complex single precision"
  else if typeChar == "I" then "unsigned integer"
  else if typeChar == "H" then "unsigned short"
  else if typeChar == "L" then "unsigned long integer"
  else if typeChar == "O" then "object"
  else if typeChar == "Q" then "unsigned long long integer"
  else if typeChar == "S" then "character"
  else if typeChar == "U" then "unicode"
  else if typeChar == "V" then "void"
  else if typeChar == "b" then "signed char"
  else if typeChar == "d" then "double precision"
  else if typeChar == "g" then "long precision"
  else if typeChar == "f" then "single precision"
  else if typeChar == "i" then "integer"
  else if typeChar == "h" then "short"
  else if typeChar == "l" then "long integer"
  else "long long integer"
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
  if IsKnownTypeChar(typeChar) {
    result := MapTypeCharToName(typeChar);
  } else {
    result := "unknown type";
  }
}
// </vc-code>
