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
  assume {:axiom} false;
}
// </vc-code>
