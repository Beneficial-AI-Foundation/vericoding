// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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