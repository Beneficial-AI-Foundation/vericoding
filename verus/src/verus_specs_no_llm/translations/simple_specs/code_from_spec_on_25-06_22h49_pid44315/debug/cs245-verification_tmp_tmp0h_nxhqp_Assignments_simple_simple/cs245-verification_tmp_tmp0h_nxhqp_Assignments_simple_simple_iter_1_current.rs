// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn simple(y: int) -> (x: int)
    requires
        y == 6
    ensures
        x == 7
{
    return 7;
}

}