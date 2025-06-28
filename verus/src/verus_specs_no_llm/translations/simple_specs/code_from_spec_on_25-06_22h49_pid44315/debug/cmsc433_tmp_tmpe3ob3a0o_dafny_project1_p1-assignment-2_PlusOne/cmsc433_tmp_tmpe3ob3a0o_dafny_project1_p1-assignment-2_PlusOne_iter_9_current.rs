use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PlusOne(x: int) -> (y: int)
    requires
        x >= 0,
    ensures
        y > 0,
{
    let result = x + 1;
    assert(x >= 0);  // proof hint: restate the precondition
    assert(result == x + 1);  // proof hint: establish the relationship
    assert(x + 1 >= 1);  // Since x >= 0, we have x + 1 >= 0 + 1 = 1
    assert(result >= 1);  // Therefore result >= 1
    assert(result > 0);  // Since result >= 1, we have result > 0
    result
}

}