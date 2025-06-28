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
    let new_x = sum - X;  // This equals Y
    let new_y = sum - new_x;  // This equals (X + Y) - Y = X
    
    // The arithmetic works as follows:
    // new_x = (X + Y) - X = Y
    // new_y = (X + Y) - new_x = (X + Y) - Y = X
    
    (new_x, new_y)
}

}