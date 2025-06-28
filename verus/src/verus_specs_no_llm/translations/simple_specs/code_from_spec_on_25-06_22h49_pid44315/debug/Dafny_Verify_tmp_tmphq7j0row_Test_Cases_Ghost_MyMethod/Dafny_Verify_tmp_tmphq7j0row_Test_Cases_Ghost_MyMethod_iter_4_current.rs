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
    assert(x >= 10);           // from precondition
    assert(result == x + 15);  // definition of result
    assert(result >= 10 + 15); // since x >= 10, we have x + 15 >= 10 + 15
    assert(result >= 25);      // since 10 + 15 == 25
    result
}

}