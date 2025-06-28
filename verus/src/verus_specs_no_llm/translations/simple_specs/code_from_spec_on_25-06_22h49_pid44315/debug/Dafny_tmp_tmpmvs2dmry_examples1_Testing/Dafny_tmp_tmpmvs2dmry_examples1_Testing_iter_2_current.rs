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
    // To satisfy the postconditions:
    // - y >= 0: we need y to be non-negative
    // - x >= 0 ==> x == y: if x is non-negative, then x must equal y
    // - x < 0 ==> -x == y: if x is negative, then -x must equal y
    // - y == abs(x): y must be the absolute value of x
    //
    // These conditions mean y = abs(x), so we can choose any x and set y = abs(x)
    // Let's choose x = 10, then y = 10, and z can be anything
    (10, 10, 0)
}

}