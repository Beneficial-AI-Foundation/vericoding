// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Triple(x: int) -> r: int)
    ensures r == 3 * x
{
    r := Average(2 * x, 4 * x);
}


// SPEC 

method Triple1(x: int) returns (r: int
    ensures r == 3 * x,
            r == 3 * x
{
}

}