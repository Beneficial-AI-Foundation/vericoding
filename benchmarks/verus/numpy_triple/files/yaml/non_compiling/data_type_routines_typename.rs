/* Return a description for the given data type code */

use vstd::prelude::*;

verus! {
fn typename(char: &str) -> (result: String)
    ensures
        (char == "S1") ==> (result@ == "character"@),
        (char == "?") ==> (result@ == "bool"@),
        (char == "B") ==> (result@ == "unsigned char"@),
        (char == "D") ==> (result@ == "complex double precision"@),
        (char == "G") ==> (result@ == "complex long double precision"@),
        (char == "F") ==> (result@ == "complex single precision"@),
        (char == "I") ==> (result@ == "unsigned integer"@),
        (char == "H") ==> (result@ == "unsigned short"@),
        (char == "L") ==> (result@ == "unsigned long integer"@),
        (char == "O") ==> (result@ == "object"@),
        (char == "Q") ==> (result@ == "unsigned long long integer"@),
        (char == "S") ==> (result@ == "character"@),
        (char == "U") ==> (result@ == "unicode"@),
        (char == "V") ==> (result@ == "void"@),
        (char == "b") ==> (result@ == "signed char"@),
        (char == "d") ==> (result@ == "double precision"@),
        (char == "g") ==> (result@ == "long precision"@),
        (char == "f") ==> (result@ == "single precision"@),
        (char == "i") ==> (result@ == "integer"@),
        (char == "h") ==> (result@ == "short"@),
        (char == "l") ==> (result@ == "long integer"@),
        (char == "q") ==> (result@ == "long long integer"@),
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
}
fn main() {}