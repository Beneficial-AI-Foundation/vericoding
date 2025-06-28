use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn swap(X: int, Y: int) -> (x: int, y: int)
    ensures
        x == Y,
        y == X,
{
    (Y, X)
}

}