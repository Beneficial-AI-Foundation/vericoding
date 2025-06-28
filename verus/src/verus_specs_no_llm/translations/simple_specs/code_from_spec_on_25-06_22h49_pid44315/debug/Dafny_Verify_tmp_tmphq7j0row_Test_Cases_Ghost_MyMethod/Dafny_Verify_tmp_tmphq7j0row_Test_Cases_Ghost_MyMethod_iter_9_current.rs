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
    
    // Proof that result >= 25
    assert(x >= 10);           // from precondition
    assert(result == x + 15);  // definition of result
    assert(x + 15 >= 10 + 15); // arithmetic property
    assert(10 + 15 == 25);     // arithmetic
    assert(result >= 25);      // transitivity
    
    result
}

}