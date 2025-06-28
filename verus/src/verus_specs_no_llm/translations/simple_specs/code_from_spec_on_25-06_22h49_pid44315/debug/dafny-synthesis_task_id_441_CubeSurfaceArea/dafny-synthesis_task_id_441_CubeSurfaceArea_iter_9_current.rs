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
    
    // Direct proof using arithmetic properties
    assert(result == 6 * size * size) by {
        // Show that size_squared equals size * size
        assert(size_squared == size * size);
        // Show that result equals 6 * size_squared
        assert(result == 6 * size_squared);
        // Use associativity of multiplication
        assert(6 * size_squared == 6 * (size * size));
        // Therefore result == 6 * size * size
    };
    
    result
}

}