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
    let result1 = AbsMethod(5);
    assert(result1 == 5);
    
    // Test with negative number
    let result2 = AbsMethod(-3);
    assert(result2 == 3);
    
    // Test with zero
    let result3 = AbsMethod(0);
    assert(result3 == 0);
    
    // Test with a larger negative number
    let result4 = AbsMethod(-1000);
    assert(result4 == 1000);
}

}