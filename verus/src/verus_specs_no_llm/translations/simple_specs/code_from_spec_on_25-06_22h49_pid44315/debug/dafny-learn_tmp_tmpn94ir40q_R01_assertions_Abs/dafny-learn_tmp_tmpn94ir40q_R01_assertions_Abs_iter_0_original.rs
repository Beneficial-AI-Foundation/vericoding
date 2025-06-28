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
        0 <= y,
        x < 0 ==> y == -x,
        x >= 0 ==> y == x
{
    return 0;
}

}