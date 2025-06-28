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
    let mut temp_x = X + Y;       // temp_x = X + Y
    let mut temp_y = temp_x - Y;  // temp_y = (X + Y) - Y = X
    
    // Proof: temp_y equals X
    assert(temp_y == X);
    
    temp_x = temp_x - temp_y;     // temp_x = (X + Y) - X = Y
    
    // Proof: temp_x equals Y
    assert(temp_x == Y);
    
    (temp_x, temp_y)
}

}