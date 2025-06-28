// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Add(x: int, y: int) -> (r: int)
    ensures
        r == x + y
{
    x + y
}

}