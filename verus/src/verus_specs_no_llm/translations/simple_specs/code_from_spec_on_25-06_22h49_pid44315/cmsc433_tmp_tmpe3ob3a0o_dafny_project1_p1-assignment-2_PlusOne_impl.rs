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
    assert(x >= 0);  // from precondition
    assert(result == x + 1);  // definition of result
    assert(x + 1 > 0) by {
        // Since x >= 0, we have x + 1 >= 0 + 1 = 1 > 0
        assert(x >= 0);
        assert(x + 1 >= 1);
        assert(1 > 0);
    };
    assert(result > 0);  // Since result == x + 1 and x + 1 > 0
    result
}

}