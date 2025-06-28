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
    
    // Proof annotations to help Verus verify the arithmetic
    assert(new_x == (X + Y) - X);
    assert(new_x == Y);
    
    assert(new_y == sum - new_x);
    assert(new_y == (X + Y) - new_x);
    assert(new_y == (X + Y) - Y);
    assert(new_y == X);
    
    (new_x, new_y)
}

}