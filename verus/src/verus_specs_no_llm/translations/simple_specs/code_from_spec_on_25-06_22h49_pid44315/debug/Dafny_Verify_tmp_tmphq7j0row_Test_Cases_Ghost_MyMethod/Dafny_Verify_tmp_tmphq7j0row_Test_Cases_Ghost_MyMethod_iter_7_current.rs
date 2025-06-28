use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MyMethod(x: int) -> (y: int)
    requires
        10 <= x
    ensures
        25 <= y
{
    let result = x + 15;
    
    // Prove that result >= 25
    assert(x >= 10);           // from precondition
    assert(result == x + 15);  // definition of result
    
    // Since x >= 10, we have x + 15 >= 10 + 15 = 25
    assert(result >= 25) by {
        assert(x >= 10);
        assert(result == x + 15);
        // Verus can handle this arithmetic directly
    };
    
    result
}

}