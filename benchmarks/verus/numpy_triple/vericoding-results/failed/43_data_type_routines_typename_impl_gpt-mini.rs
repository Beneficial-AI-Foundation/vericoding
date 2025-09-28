// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert &str to verus String preserving view */
fn string_from_literal(s: &str) -> (result: String)
    ensures
        result@ == s@,
{
    let result = String::from_str(s);
    result
}
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
    /* code modified by LLM (iteration 5): compare &str directly and map to descriptions using string_from_literal */
    if char == "S1" {
        string_from_literal("character")
    } else if char == "?" {
        string_from_literal("bool")
    } else if char == "B" {
        string_from_literal("unsigned char")
    } else if char == "D" {
        string_from_literal("complex double precision")
    } else if char == "G" {
        string_from_literal("complex long double precision")
    } else if char == "F" {
        string_from_literal("complex single precision")
    } else if char == "I" {
        string_from_literal("unsigned integer")
    } else if char == "H" {
        string_from_literal("unsigned short")
    } else if char == "L" {
        string_from_literal("unsigned long integer")
    } else if char == "O" {
        string_from_literal("object")
    } else if char == "Q" {
        string_from_literal("unsigned long long integer")
    } else if char == "S" {
        string_from_literal("character")
    } else if char == "U" {
        string_from_literal("unicode")
    } else if char == "V" {
        string_from_literal("void")
    } else if char == "b" {
        string_from_literal("signed char")
    } else if char == "d" {
        string_from_literal("double precision")
    } else if char == "g" {
        string_from_literal("long precision")
    } else if char == "f" {
        string_from_literal("single precision")
    } else if char == "i" {
        string_from_literal("integer")
    } else if char == "h" {
        string_from_literal("short")
    } else if char == "l" {
        string_from_literal("long integer")
    } else if char == "q" {
        string_from_literal("long long integer")
    } else {
        string_from_literal(char)
    }
}
// </vc-code>


}
fn main() {}