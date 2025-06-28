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
    // Choose a negative value for x to test both branches
    let x_val = -5;
    
    // Calculate y as the absolute value of x
    let y_val = if x_val >= 0 { x_val } else { -x_val };
    
    // z can be any value since it's not constrained
    let z_val = 0;
    
    // The postconditions will be checked against the returned tuple (y, x, z)
    // So we need: y >= 0, x >= 0 ==> x == y, x < 0 ==> -x == y, y == abs(x)
    
    (y_val, x_val, z_val)
}

}