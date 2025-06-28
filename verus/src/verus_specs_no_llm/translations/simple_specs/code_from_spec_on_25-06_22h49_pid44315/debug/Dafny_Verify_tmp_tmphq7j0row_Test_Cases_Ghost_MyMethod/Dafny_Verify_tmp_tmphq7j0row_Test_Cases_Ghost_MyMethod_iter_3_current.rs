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
    assert(10 + 15 == 25);
    assert(x >= 10);
    assert(x + 15 >= 10 + 15); // x >= 10 implies x + 15 >= 10 + 15
    assert(10 + 15 == 25);     // we know 10 + 15 = 25
    assert(result >= 25);      // therefore x + 15 >= 25
    result
}

}