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
    assert(new_x == Y) by {
        // (X + Y) - X == Y by arithmetic
    };
    
    assert(new_y == sum - new_x);
    assert(new_y == (X + Y) - Y) by {
        assert(new_x == Y);  // From above
        assert(sum - new_x == (X + Y) - Y);  // Substitution
    };
    assert(new_y == X) by {
        // (X + Y) - Y == X by arithmetic
    };
    
    (new_x, new_y)
}

}