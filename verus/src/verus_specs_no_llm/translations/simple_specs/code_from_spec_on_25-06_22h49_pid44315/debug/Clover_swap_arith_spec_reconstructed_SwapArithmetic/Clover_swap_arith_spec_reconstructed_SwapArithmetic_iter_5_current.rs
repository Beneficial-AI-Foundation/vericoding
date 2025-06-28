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
    
    // Proof annotation: help Verus understand that temp_y equals X
    assert(temp_y == (X + Y) - Y) by {
        // This follows from the definition of temp_y
    };
    assert(temp_y == X) by {
        // Arithmetic: (X + Y) - Y = X
        assert((X + Y) - Y == X);
    };
    
    temp_x = temp_x - temp_y;     // temp_x = (X + Y) - X = Y
    
    // Proof annotation: help Verus understand that temp_x equals Y
    assert(temp_x == (X + Y) - temp_y) by {
        // This follows from the assignment
    };
    assert(temp_x == (X + Y) - X) by {
        // Since temp_y == X
        assert(temp_y == X);
    };
    assert(temp_x == Y) by {
        // Arithmetic: (X + Y) - X = Y
        assert((X + Y) - X == Y);
    };
    
    // Final verification
    assert(temp_x == Y);
    assert(temp_y == X);
    
    (temp_x, temp_y)
}

}