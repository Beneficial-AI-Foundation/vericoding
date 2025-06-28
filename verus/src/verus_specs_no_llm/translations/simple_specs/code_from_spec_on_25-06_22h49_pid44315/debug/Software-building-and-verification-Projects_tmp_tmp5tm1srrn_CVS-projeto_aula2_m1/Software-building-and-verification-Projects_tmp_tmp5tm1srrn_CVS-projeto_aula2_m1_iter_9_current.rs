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
    // - x >= 1 (since x > 0)
    // - y > x, so y > 0
    // 
    // Returning 0 satisfies all conditions:
    // - z >= 0: 0 >= 0 ✓
    // - z < y: 0 < y ✓ (since 0 < x < y implies y > 0)
    // - z != x: 0 != x ✓ (since x > 0 implies x != 0)
    
    // Proof assertions to help Verus verify the postconditions
    assert(0 < x);  // from precondition
    assert(x < y);  // from precondition
    assert(0 < y);  // follows from 0 < x < y
    assert(0 != x); // follows from 0 < x
    
    0
}

}