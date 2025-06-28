use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Forbid42(x: int, y: int) -> (z: int)
    requires y != 42
    ensures z == x/(42-y)
{
    // Since y != 42, we know 42 - y != 0
    assert(42 - y != 0);
    x / (42 - y)
}

fn Allow42(x: int, y: int) -> (z: int, err: bool) 
    ensures y != 42 ==> z == x/(42-y) && err == false
    ensures y == 42 ==> z == 0 && err == true
{
    if y == 42 {
        (0, true)
    } else {
        // When y != 42, we know 42 - y != 0
        assert(42 - y != 0);
        (x / (42 - y), false)
    }
}

fn TEST1(x: int, y: int) -> (z: int, err: bool)
    requires y != 42
    ensures z == x/(42-y)
    ensures err == false
{
    // Since we have the precondition y != 42, we know y != 42 is true
    // So we can call Allow42 and the result will satisfy our postconditions
    let result = Allow42(x, y);
    
    // Add proof assertion to help Verus verify the postconditions
    assert(y != 42);  // This is guaranteed by the precondition
    assert(42 - y != 0); // This follows from y != 42
    
    result
}

}