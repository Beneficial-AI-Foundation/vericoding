// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        y>=0;,
        x>=0 ==> x == y;,
        x<0 ==> -x == y;,
        y == abs(x); // use this instead of line 3,4
{
    return 0;
}

}