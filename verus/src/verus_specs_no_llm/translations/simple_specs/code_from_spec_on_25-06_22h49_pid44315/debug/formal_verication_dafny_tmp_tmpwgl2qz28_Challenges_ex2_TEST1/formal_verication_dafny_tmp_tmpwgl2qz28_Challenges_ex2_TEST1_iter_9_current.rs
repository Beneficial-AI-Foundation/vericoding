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
    // Since we have the precondition y != 42, we can call Allow42
    let (result_z, result_err) = Allow42(x, y);
    
    // Proof that the postcondition holds
    proof {
        // From precondition: y != 42
        // From Allow42's postcondition: y != 42 ==> result_z == x/(42-y) && result_err == false
        // By modus ponens: result_z == x/(42-y) && result_err == false
        assert(y != 42); // from precondition
        assert(result_z == x/(42-y)); // follows from Allow42's postcondition
        assert(result_err == false); // follows from Allow42's postcondition
    }
    
    (result_z, result_err)
}

}