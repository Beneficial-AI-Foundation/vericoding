use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn m1(x: int, y: int) -> (z: int)
    requires
        0 < x < y
    ensures
        z >= 0 && z < y && z != x
{
    // Since 0 < x < y, we know:
    // - x >= 1 (since x > 0 and x is int)
    // - y >= 2 (since y > x >= 1)
    // 
    // Returning 0 satisfies all conditions:
    // - z >= 0: 0 >= 0 ✓
    // - z < y: 0 < y ✓ (since y >= 2)
    // - z != x: 0 != x ✓ (since x >= 1)
    
    assert(x >= 1) by {
        // From 0 < x, we know x >= 1
    };
    assert(y >= 2) by {
        // From x < y and x >= 1, we know y >= 2
    };
    assert(0 < y) by {
        // From y >= 2
    };
    assert(0 != x) by {
        // From x >= 1, we know x != 0
    };
    
    0
}

}