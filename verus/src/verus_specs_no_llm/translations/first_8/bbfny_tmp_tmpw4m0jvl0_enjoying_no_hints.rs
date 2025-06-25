// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MultipleReturns(x: int, y: int) -> (more: int, less: int)
    requires
        0 < y
    ensures
        less < x < more
{
    return (0, 0);
}

}