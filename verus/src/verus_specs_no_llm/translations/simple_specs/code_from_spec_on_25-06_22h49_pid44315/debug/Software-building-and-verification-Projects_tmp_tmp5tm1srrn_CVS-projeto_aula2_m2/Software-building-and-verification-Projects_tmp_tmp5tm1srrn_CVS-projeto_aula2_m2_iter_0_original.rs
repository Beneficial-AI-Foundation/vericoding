// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn m2(x: nat) -> (y: int)
    requires
        x <= -1
    ensures
        y > x && y < x
{
    return 0;
}

}