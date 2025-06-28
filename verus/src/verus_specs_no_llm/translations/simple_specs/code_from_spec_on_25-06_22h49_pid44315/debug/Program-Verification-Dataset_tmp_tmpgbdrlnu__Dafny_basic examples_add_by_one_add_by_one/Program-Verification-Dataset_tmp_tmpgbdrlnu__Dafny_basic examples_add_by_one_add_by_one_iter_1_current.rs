// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_by_one(x: int, y: int) -> (r: int)
    requires
        y >= 0
    ensures
        r == x + y
{
    return x + y;
}

}