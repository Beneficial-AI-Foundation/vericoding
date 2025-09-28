// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no extra helpers required; placeholder to keep helpers section valid */
proof fn helper_placeholder_iter5() { }
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
{
    /* code modified by LLM (iteration 5): switch to &str equality comparisons; avoid unsupported byte literals */
    let result =
        if char == "S1" { String::from("character") }
        else if char == "?" { String::from("bool") }
        else if char == "B" { String::from("unsigned char") }
        else if char == "D" { String::from("complex double precision") }
        else if char == "G" { String::from("complex long double precision") }
        else if char == "F" { String::from("complex single precision") }
        else if char == "I" { String::from("unsigned integer") }
        else if char == "H" { String::from("unsigned short") }
        else if char == "L" { String::from("unsigned long integer") }
        else if char == "O" { String::from("object") }
        else if char == "Q" { String::from("unsigned long long integer") }
        else if char == "S" { String::from("character") }
        else if char == "U" { String::from("unicode") }
        else if char == "V" { String::from("void") }
        else if char == "b" { String::from("signed char") }
        else if char == "d" { String::from("double precision") }
        else if char == "g" { String::from("long precision") }
        else if char == "f" { String::from("single precision") }
        else if char == "i" { String::from("integer") }
        else if char == "h" { String::from("short") }
        else if char == "l" { String::from("long integer") }
        else if char == "q" { String::from("long long integer") }
        else { String::from("unknown type") };
    result
}
// </vc-code>


}
fn main() {}