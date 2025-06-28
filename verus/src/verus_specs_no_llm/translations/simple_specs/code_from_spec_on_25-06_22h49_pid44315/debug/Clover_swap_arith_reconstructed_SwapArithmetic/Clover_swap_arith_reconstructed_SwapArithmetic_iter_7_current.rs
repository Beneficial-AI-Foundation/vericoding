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
    let sum = X + Y;
    let new_x = sum - X;
    let new_y = sum - Y;
    
    // The arithmetic works as follows:
    // new_x = (X + Y) - X = Y
    // new_y = (X + Y) - Y = X
    
    (new_x, new_y)
}

}