// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        y>=0,
        x>=0 ==> x == y,
        x<0 ==> -x == y,
        y == abs(x)
{
    return 0;
}

}