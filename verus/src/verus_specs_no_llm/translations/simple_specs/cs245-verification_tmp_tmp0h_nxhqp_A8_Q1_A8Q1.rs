// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn power(a: int, n: int) -> int //function for a to the power of n
    requires
        0 <= n


// SPEC


method A8Q1(y0: int, x: int) returns (z: int),
        y0 >= 0
/*Post-Condition*/
    ensures
        z==power(x,y0)
{
    0
}

spec fn spec_A8Q1(y0: int, x: int) -> z: int
    requires
        y0 >= 0
/*Post-Condition*/
    ensures
        z==power(x,y0)
;

proof fn lemma_A8Q1(y0: int, x: int) -> (z: int)
    requires
        y0 >= 0
/*Post-Condition*/
    ensures
        z==power(x,y0)
{
    0
}

}