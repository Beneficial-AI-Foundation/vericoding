// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sqrt(x: int, r: int) -> bool {
    r*r <= x && (r+1)*(r+1) > x
}

spec fn spec_mySqrt(x: int) -> res: int
    requires
        0 <= x
    ensures
        sqrt(x, res)
;

proof fn lemma_mySqrt(x: int) -> (res: int)
    requires
        0 <= x
    ensures
        sqrt(x, res)
{
    0
}

}