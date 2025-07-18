use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for specifications
spec fn Abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// Executable method version
method AbsMethod(x: i32) -> (y: i32)
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

// Test method that calls AbsMethod and verifies its properties
method TestingAbs()
{
    let result1 = AbsMethod(5);
    assert(result1 == 5);
    
    let result2 = AbsMethod(-3);
    assert(result2 == 3);
    
    let result3 = AbsMethod(0);
    assert(result3 == 0);
}

}