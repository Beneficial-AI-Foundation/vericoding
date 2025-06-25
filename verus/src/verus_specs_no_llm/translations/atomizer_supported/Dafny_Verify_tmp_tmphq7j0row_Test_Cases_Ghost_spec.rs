// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Triple(x: int) -> (r: int)
    ensures r == 3 * x
{
    r := Average(2 * x, 4 * x);
}


// SPEC 

method Triple1(x: int) returns (r: int)
    ensures
        r == 3 * x,
        r == 3 * x
{
    return (0, 0);
}

}