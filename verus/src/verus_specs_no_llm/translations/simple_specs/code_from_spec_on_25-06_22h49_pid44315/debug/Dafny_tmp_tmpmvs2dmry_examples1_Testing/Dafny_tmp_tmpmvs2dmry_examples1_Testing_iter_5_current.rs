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
    // Choose values that satisfy the postconditions
    // The postconditions require that y == abs(x)
    // Let's choose x = 5, then y must be abs(5) = 5
    let x_val = 5;
    let y_val = Abs(x_val);
    let z_val = 0;
    
    // The verifier should be able to prove these automatically given the Abs function's postconditions
    (y_val, x_val, z_val)
}

}