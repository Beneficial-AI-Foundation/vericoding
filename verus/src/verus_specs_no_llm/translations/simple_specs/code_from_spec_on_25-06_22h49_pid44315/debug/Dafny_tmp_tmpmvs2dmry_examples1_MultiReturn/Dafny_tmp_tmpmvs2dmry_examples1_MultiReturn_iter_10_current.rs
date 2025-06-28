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
        // Since y >= 0, we have -y <= 0, so x - y <= x + 0 = x
        assert(y >= 0);
        assert(-y <= 0);
        assert(x - y <= x + 0);
        assert(x + 0 == x);
    };
    
    assert(x <= more) by {
        // Since y >= 0, we have x = x + 0 <= x + y
        assert(y >= 0);
        assert(x + 0 <= x + y);
        assert(x + 0 == x);
    };
    
    (more, less)
}

}