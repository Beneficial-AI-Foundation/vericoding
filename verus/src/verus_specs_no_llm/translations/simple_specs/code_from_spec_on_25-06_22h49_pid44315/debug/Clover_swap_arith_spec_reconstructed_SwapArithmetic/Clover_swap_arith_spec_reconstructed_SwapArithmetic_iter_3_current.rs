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
    let mut temp_x = X + Y;
    let mut temp_y = temp_x - Y;  // temp_y = (X + Y) - Y = X
    temp_x = temp_x - temp_y;     // temp_x = (X + Y) - X = Y
    
    // Verification help: assert the intermediate values
    assert(temp_y == X);
    assert(temp_x == Y);
    
    (temp_x, temp_y)
}

}