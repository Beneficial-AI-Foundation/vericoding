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
    requires
        x < 0
    ensures
        0 < y,
        y == -x
{
    return 0;
}

}