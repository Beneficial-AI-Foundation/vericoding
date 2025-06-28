// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Min(x: int, y: int) -> (r: int)
    ensures
        r <= x && r <= y,
        r == x || r == y
{
    if x <= y {
        x
    } else {
        y
    }
}

}