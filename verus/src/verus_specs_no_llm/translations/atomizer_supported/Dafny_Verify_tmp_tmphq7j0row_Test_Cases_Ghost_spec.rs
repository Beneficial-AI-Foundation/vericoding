// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Average(a: int, b: int) -> int
{
    0
}

proof fn Triple(x: int) -> (r: int)
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
    (0, 0)
}

}