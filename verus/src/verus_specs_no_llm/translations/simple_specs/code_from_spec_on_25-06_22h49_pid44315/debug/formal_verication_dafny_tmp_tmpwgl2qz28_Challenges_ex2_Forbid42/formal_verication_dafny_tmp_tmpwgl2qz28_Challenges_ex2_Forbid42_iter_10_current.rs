use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Forbid42(x: int, y: int) -> (z: int)
    requires
        y != 42
    ensures
        z == x/(42-y)
{
    let divisor = 42 - y;
    
    // Prove that divisor is non-zero
    assert(divisor != 0) by {
        assert(y != 42); // from requires clause
        assert(42 - y != 0); // since y != 42, then 42 - y != 0
    };
    
    // Perform the division
    x / divisor
}

}