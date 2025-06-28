use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    requires
        x < 0
    ensures
        0 < y,
        y == -x
{
    let result = -x;
    assert(x < 0);  // From precondition
    assert(result == -x);  // By definition
    assert(0 < result) by {
        // Since x < 0, we have -x > 0
        assert(x < 0);
        assert(-x > -0);
        assert(-x > 0);
    };
    result
}

}