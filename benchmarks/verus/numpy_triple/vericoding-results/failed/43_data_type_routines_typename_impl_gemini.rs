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
{
    /* code modified by LLM (iteration 5): Added proof blocks with assertions to explicitly guide the verifier in proving the equality between string literals and their sequence representations. */
    match char {
        "S1" => {
            proof { assert(("character")@ == seq!['c','h','a','r','a','c','t','e','r']); }
            String::from_str("character")
        },
        "?" => {
            proof { assert(("bool")@ == seq!['b','o','o','l']); }
            String::from_str("bool")
        },
        "B" => {
            proof { assert(("unsigned char")@ == seq!['u','n','s','i','g','n','e','d',' ','c','h','a','r']); }
            String::from_str("unsigned char")
        },
        "D" => {
            proof { assert(("complex double precision")@ == seq!['c','o','m','p','l','e','x',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']); }
            String::from_str("complex double precision")
        },
        "G" => {
            proof { assert(("complex long double precision")@ == seq!['c','o','m','p','l','e','x',' ','l','o','n','g',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']); }
            String::from_str("complex long double precision")
        },
        "F" => {
            proof { assert(("complex single precision")@ == seq!['c','o','m','p','l','e','x',' ','s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']); }
            String::from_str("complex single precision")
        },
        "I" => {
            proof { assert(("unsigned integer")@ == seq!['u','n','s','i','g','n','e','d',' ','i','n','t','e','g','e','r']); }
            String::from_str("unsigned integer")
        },
        "H" => {
            proof { assert(("unsigned short")@ == seq!['u','n','s','i','g','n','e','d',' ','s','h','o','r','t']); }
            String::from_str("unsigned short")
        },
        "L" => {
            proof { assert(("unsigned long integer")@ == seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','i','n','t','e','g','e','r']); }
            String::from_str("unsigned long integer")
        },
        "O" => {
            proof { assert(("object")@ == seq!['o','b','j','e','c','t']); }
            String::from_str("object")
        },
        "Q" => {
            proof { assert(("unsigned long long integer")@ == seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']); }
            String::from_str("unsigned long long integer")
        },
        "S" => {
            proof { assert(("character")@ == seq!['c','h','a','r','a','c','t','e','r']); }
            String::from_str("character")
        },
        "U" => {
            proof { assert(("unicode")@ == seq!['u','n','i','c','o','d','e']); }
            String::from_str("unicode")
        },
        "V" => {
            proof { assert(("void")@ == seq!['v','o','i','d']); }
            String::from_str("void")
        },
        "b" => {
            proof { assert(("signed char")@ == seq!['s','i','g','n','e','d',' ','c','h','a','r']); }
            String::from_str("signed char")
        },
        "d" => {
            proof { assert(("double precision")@ == seq!['d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']); }
            String::from_str("double precision")
        },
        "g" => {
            proof { assert(("long precision")@ == seq!['l','o','n','g',' ','p','r','e','c','i','s','i','o','n']); }
            String::from_str("long precision")
        },
        "f" => {
            proof { assert(("single precision")@ == seq!['s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']); }
            String::from_str("single precision")
        },
        "i" => {
            proof { assert(("integer")@ == seq!['i','n','t','e','g','e','r']); }
            String::from_str("integer")
        },
        "h" => {
            proof { assert(("short")@ == seq!['s','h','o','r','t']); }
            String::from_str("short")
        },
        "l" => {
            proof { assert(("long integer")@ == seq!['l','o','n','g',' ','i','n','t','e','g','e','r']); }
            String::from_str("long integer")
        },
        "q" => {
            proof { assert(("long long integer")@ == seq!['l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']); }
            String::from_str("long long integer")
        },
        _ => String::from_str(char),
    }
}
// </vc-code>


}
fn main() {}