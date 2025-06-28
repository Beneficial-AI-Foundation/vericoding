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
    
    // Proof block to help Verus verify the postconditions
    proof {
        assert(sum == X + Y);
        assert(new_x == sum - X);
        assert(new_x == (X + Y) - X);
        assert(new_x == Y) by {
            assert((X + Y) - X == Y);
        };
        assert(new_y == sum - Y);
        assert(new_y == (X + Y) - Y);
        assert(new_y == X) by {
            assert((X + Y) - Y == X);
        };
    }
    
    (new_x, new_y)
}

}