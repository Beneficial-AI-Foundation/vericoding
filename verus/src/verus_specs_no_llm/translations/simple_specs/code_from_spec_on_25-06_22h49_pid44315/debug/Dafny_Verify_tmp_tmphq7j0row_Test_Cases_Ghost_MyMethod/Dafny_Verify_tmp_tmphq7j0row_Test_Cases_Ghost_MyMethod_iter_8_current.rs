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
    assert(result >= 25);      // this follows from the above two assertions
    
    result
}

}