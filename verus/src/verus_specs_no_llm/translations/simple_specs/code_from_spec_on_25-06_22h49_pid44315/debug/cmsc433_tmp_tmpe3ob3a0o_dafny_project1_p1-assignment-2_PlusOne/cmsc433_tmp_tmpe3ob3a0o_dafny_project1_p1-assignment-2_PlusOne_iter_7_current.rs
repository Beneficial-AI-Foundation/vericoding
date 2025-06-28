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
    assert(result > 0) by {
        // Since x >= 0, we have x + 1 >= 1, therefore x + 1 > 0
    };
    result
}

}