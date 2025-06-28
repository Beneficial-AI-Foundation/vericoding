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
    let temp_x = X + Y;       // temp_x = X + Y
    let temp_y = temp_x - Y;  // temp_y = (X + Y) - Y = X
    
    // Proof: temp_y equals X
    assert(temp_x == X + Y);
    assert(temp_y == temp_x - Y);
    assert(temp_y == (X + Y) - Y) by {
        assert(temp_x == X + Y);
    };
    assert(temp_y == X) by (arithmetic);
    
    let final_x = temp_x - temp_y;     // final_x = (X + Y) - X = Y
    
    // Proof: final_x equals Y
    assert(final_x == temp_x - temp_y);
    assert(final_x == (X + Y) - X) by {
        assert(temp_x == X + Y);
        assert(temp_y == X);
    };
    assert(final_x == Y) by (arithmetic);
    
    // Final verification that the postconditions hold
    assert(final_x == Y);
    assert(temp_y == X);
    
    (final_x, temp_y)
}

}