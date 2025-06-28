use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CubeSurfaceArea(size: int) -> (area: int)
    requires
        size > 0,
    ensures
        area == 6 * size * size,
{
    let size_squared = size * size;
    let result = 6 * size_squared;
    
    // Proof that result equals 6 * size * size
    assert(result == 6 * size_squared) by {
        // This follows directly from the definition of result
    };
    assert(size_squared == size * size) by {
        // This follows directly from the definition of size_squared
    };
    assert(result == 6 * size * size) by {
        // By transitivity: result == 6 * size_squared == 6 * (size * size)
    };
    
    result
}

}