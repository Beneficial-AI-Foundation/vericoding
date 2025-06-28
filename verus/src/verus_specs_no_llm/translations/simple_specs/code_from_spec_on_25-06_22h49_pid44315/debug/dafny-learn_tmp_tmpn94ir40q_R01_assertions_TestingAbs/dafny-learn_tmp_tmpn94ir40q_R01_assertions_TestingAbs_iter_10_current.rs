use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for specifications
spec fn Abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// Executable function version
fn AbsMethod(x: i32) -> (y: i32)
    requires x > i32::MIN, // Prevent overflow
    ensures 0 <= y,
    ensures x < 0 ==> y == -x,
    ensures x >= 0 ==> y == x,
    ensures y == Abs(x as int),
{
    if x < 0 {
        -x
    } else {
        x
    }
}

// Test function that calls AbsMethod and verifies its properties
fn TestingAbs()
{
    // Test with positive number
    assert(5 > i32::MIN);
    let result1 = AbsMethod(5);
    // The postcondition ensures x >= 0 ==> y == x, so result1 == 5
    assert(result1 == 5);
    
    // Test with negative number
    assert(-3 > i32::MIN);
    let result2 = AbsMethod(-3);
    // The postcondition ensures x < 0 ==> y == -x, so result2 == -(-3) == 3
    assert(result2 == 3);
    
    // Test with zero
    assert(0 > i32::MIN);
    let result3 = AbsMethod(0);
    // The postcondition ensures x >= 0 ==> y == x, so result3 == 0
    assert(result3 == 0);
    
    // Test with a larger negative number
    assert(-1000 > i32::MIN);
    let result4 = AbsMethod(-1000);
    // The postcondition ensures x < 0 ==> y == -x, so result4 == -(-1000) == 1000
    assert(result4 == 1000);
}

}