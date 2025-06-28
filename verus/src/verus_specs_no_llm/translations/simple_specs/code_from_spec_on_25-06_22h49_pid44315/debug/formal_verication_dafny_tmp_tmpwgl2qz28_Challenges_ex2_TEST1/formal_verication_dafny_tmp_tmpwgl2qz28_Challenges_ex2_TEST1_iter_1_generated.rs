use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Forbid42(x: int, y: int) -> (z: int)
    requires y != 42
    ensures z == x/(42-y)
{
    x / (42 - y)
}

fn Allow42(x: int, y: int) -> (z: int, err: bool) 
    ensures y != 42 ==> z == x/(42-y) && err == false
    ensures y == 42 ==> z == 0 && err == true
{
    if y == 42 {
        (0, true)
    } else {
        (x / (42 - y), false)
    }
}

fn TEST1(x: int, y: int) -> (z: int, err: bool)
    requires y != 42
    ensures z == x/(42-y)
    ensures y != 42 ==> z == x/(42-y) && err == false
    ensures y == 42 ==> z == 0 && err == true
{
    // Since we have the precondition y != 42, we know y != 42 is true
    // So we can call Allow42 and the result will satisfy our postconditions
    Allow42(x, y)
}

}