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
    // The postconditions relate the returned values y and x
    // We need: y >= 0, and y == abs(x)
    // Let's choose x = 5, then y must be abs(5) = 5
    let x_val = 5;
    let y_val = 5; // This is abs(5)
    let z_val = 0;
    
    // Verify the postconditions:
    // y >= 0: 5 >= 0 ✓
    // x >= 0 ==> x == y: 5 >= 0 ==> 5 == 5 ✓
    // x < 0 ==> -x == y: false ==> anything ✓ 
    // y == abs(x): 5 == abs(5) ✓
    
    (y_val, x_val, z_val)
}

}