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
  match typeChar {
    case "S1" => result := "character";
    case "?" => result := "bool";
    case "B" => result := "unsigned char";
    case "D" => result := "complex double precision";
    case "G" => result := "complex long double precision";
    case "F" => result := "complex single precision";
    case "I" => result := "unsigned integer";
    case "H" => result := "unsigned short";
    case "L" => result := "unsigned long integer";
    case "O" => result := "object";
    case "Q" => result := "unsigned long long integer";
    case "S" => result := "character";
    case "U" => result := "unicode";
    case "V" => result := "void";
    case "b" => result := "signed char";
    case "d" => result := "double precision";
    case "g" => result := "long precision";
    case "f" => result := "single precision";
    case "i" => result := "integer";
    case "h" => result := "short";
    case "l" => result := "long integer";
    case "q" => result := "long long integer";
    case _ => result := "unknown type";
  }
}
// </vc-code>
