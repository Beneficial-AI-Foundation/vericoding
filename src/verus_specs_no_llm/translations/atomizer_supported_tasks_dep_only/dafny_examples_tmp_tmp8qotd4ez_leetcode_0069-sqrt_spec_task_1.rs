// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn sqrt(x: int, r: int) -> bool {
    r*r <= x and (r+1)*(r+1) > x
}

fn mySqrt(x: int) -> (res: int)
    requires 0 <= x;
    ensures sqrt(x, res);
{
}

}