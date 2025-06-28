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
    let new_y = sum - Y;  // This equals X
    
    // The arithmetic is straightforward enough that Verus should verify automatically
    // but we can add explicit proof steps if needed
    proof {
        assert(sum == X + Y);
        assert(new_x == sum - X);
        assert(new_x == (X + Y) - X);
        assert(new_x == Y) by(arithmetic);
        assert(new_y == sum - Y);
        assert(new_y == (X + Y) - Y);
        assert(new_y == X) by(arithmetic);
    }
    
    (new_x, new_y)
}

}

The key changes I made:


The arithmetic swap algorithm works by:
- Computing `sum = X + Y`
- Setting `new_x = sum - X = (X + Y) - X = Y`
- Setting `new_y = sum - Y = (X + Y) - Y = X`

This satisfies the postcondition that the returned values are swapped versions of the inputs.