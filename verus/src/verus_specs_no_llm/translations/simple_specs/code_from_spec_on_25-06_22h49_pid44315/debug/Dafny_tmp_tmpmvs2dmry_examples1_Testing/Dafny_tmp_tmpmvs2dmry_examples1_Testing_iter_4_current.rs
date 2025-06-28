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
    // - y >= 0 (first return value)
    // - if x >= 0 then x == y (if second return value >= 0, then second == first)
    // - if x < 0 then -x == y (if second return value < 0, then -second == first)
    // - y == abs(x) (first return value == abs(second return value))
    //
    // This means the first return value (y) must be the absolute value of the second return value (x)
    let x_val = 10;
    let y_val = Abs(x_val);
    let z_val = 0;
    
    // Explicit assertions to help the verifier
    assert(y_val >= 0);
    assert(x_val >= 0 ==> x_val == y_val);
    assert(x_val < 0 ==> -x_val == y_val);
    assert(y_val == abs(x_val));
    
    (y_val, x_val, z_val)
}

}