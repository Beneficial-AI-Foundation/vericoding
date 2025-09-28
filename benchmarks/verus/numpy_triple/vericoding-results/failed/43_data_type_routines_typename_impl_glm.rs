// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn typename(char: &str) -> (result: String)
    ensures
        /* Known type code mappings from NumPy documentation */
        (char == "S1" ==> result@ == seq!['c','h','a','r','a','c','t','e','r']) &&
        (char == "?" ==> result@ == seq!['b','o','o','l']) &&
        (char == "B" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','c','h','a','r']) &&
        (char == "D" ==> result@ == seq!['c','o','m','p','l','e','x',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "G" ==> result@ == seq!['c','o','m','p','l','e','x',' ','l','o','n','g',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "F" ==> result@ == seq!['c','o','m','p','l','e','x',' ','s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "I" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','i','n','t','e','g','e','r']) &&
        (char == "H" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','s','h','o','r','t']) &&
        (char == "L" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        (char == "O" ==> result@ == seq!['o','b','j','e','c','t']) &&
        (char == "Q" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        (char == "S" ==> result@ == seq!['c','h','a','r','a','c','t','e','r']) &&
        (char == "U" ==> result@ == seq!['u','n','i','c','o','d','e']) &&
        (char == "V" ==> result@ == seq!['v','o','i','d']) &&
        (char == "b" ==> result@ == seq!['s','i','g','n','e','d',' ','c','h','a','r']) &&
        (char == "d" ==> result@ == seq!['d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "g" ==> result@ == seq!['l','o','n','g',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "f" ==> result@ == seq!['s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "i" ==> result@ == seq!['i','n','t','e','g','e','r']) &&
        (char == "h" ==> result@ == seq!['s','h','o','r','t']) &&
        (char == "l" ==> result@ == seq!['l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        (char == "q" ==> result@ == seq!['l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        /* For unknown type codes, return default description */
        (char != "S1" && char != "?" && char != "B" && char != "D" && 
         char != "G" && char != "F" && char != "I" && char != "H" && 
         char != "L" && char != "O" && char != "Q" && char != "S" && 
         char != "U" && char != "V" && char != "b" && char != "d" && 
         char != "g" && char != "f" && char != "i" && char != "h" && 
         char != "l" && char != "q" ==>
         (result@ == seq!['u','n','k','n','o','w','n',' ','t','y','p','e'] || result@ == char@)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed unknown case to return the input string */
{
    match char {
        "S1" => "character".to_string(),
        "?" => "bool".to_string(),
        "B" => "unsigned char".to_string(),
        "D" => "complex double precision".to_string(),
        "G" => "complex long double precision".to_string(),
        "F" => "complex single precision".to_string(),
        "I" => "unsigned integer".to_string(),
        "H" => "unsigned short".to_string(),
        "L" => "unsigned long integer".to_string(),
        "O" => "object".to_string(),
        "Q" => "unsigned long long integer".to_string(),
        "S" => "character".to_string(),
        "U" => "unicode".to_string(),
        "V" => "void".to_string(),
        "b" => "signed char".to_string(),
        "d" => "double precision".to_string(),
        "g" => "long precision".to_string(),
        "f" => "single precision".to_string(),
        "i" => "integer".to_string(),
        "h" => "short".to_string(),
        "l" => "long integer".to_string(),
        "q" => "long long integer".to_string(),
        _ => char.to_string(),
    }
}
// </vc-code>


}
fn main() {}