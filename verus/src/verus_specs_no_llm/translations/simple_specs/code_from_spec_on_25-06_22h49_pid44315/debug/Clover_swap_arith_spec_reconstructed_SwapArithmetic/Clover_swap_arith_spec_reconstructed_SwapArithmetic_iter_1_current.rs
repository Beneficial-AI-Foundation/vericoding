// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapArithmetic(X: int, Y: int) -> (x: int, y: int)
    ensures
        x == Y,
        y == X
{
    let mut x = X + Y;
    let mut y = x - Y;  // y = (X + Y) - Y = X
    x = x - y;          // x = (X + Y) - X = Y
    return (x, y);
}

}