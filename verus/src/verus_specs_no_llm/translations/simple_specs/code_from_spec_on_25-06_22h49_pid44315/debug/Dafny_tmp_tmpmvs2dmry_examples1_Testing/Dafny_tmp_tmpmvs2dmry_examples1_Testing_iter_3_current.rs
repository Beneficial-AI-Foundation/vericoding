use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures 
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == abs(x)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

// ATOM - spec function for absolute value
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// SPEC - method returning multiple values
fn Testing() -> (y: int, x: int, z: int)
    ensures 
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == abs(x)
{
    // To satisfy the postconditions, we need to ensure that:
    // - y >= 0
    // - if x >= 0 then x == y
    // - if x < 0 then -x == y  
    // - y == abs(x)
    //
    // This means y must be the absolute value of x
    // We can choose x = 10, then y = abs(10) = 10
    let x = 10;
    let y = Abs(x);
    let z = 0;
    
    // The postconditions will be satisfied because:
    // - y = Abs(10) = 10 >= 0 ✓
    // - x = 10 >= 0, and x == y (both are 10) ✓
    // - y = 10 == abs(10) ✓
    (y, x, z)
}

}