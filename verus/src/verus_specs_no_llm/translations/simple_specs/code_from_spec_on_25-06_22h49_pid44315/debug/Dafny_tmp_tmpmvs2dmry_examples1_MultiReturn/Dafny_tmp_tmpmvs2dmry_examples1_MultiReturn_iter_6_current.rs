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
    assert(less <= x) by {
        assert(x - y <= x);
    };
    assert(x <= more) by {
        assert(x <= x + y);
    };
    
    (more, less)
}

}