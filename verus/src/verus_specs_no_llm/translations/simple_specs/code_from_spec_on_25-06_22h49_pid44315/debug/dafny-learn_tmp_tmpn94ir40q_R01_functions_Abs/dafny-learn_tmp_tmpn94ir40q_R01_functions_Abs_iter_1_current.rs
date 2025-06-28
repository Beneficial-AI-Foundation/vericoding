// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        abs(x) == y
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

}