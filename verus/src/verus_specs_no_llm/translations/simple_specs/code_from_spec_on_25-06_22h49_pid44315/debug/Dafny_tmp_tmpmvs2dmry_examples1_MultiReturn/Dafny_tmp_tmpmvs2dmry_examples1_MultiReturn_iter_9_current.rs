use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MultiReturn(x: int, y: int) -> (more: int, less: int)
    requires
        y >= 0
    ensures
        less <= x <= more
{
    let more = x + y;
    let less = x - y;
    
    // Proof assertions to help Verus verify the postcondition
    assert(y >= 0);  // From precondition
    assert(less == x - y);
    assert(more == x + y);
    assert(less <= x) by {
        assert(x - y <= x);  // Since y >= 0
    };
    assert(x <= more) by {
        assert(x <= x + y);  // Since y >= 0
    };
    
    (more, less)
}

}