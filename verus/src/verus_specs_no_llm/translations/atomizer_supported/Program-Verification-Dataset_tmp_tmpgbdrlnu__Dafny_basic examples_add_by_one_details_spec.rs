// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn plus_one(x: int) -> (r: int)
    requires
        x >= 0
    ensures
        r == x + 1
{
    return 0;
}

}