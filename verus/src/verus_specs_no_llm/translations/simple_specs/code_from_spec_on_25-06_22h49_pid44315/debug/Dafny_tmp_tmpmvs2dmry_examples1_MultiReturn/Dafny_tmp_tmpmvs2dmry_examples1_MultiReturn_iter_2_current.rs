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
    
    // Proof annotations to help Verus verify the postcondition
    assert(y >= 0);
    assert(more == x + y);
    assert(less == x - y);
    assert(less <= x) by {
        // Since y >= 0, we have x - y <= x
        assert(x - y <= x);
    };
    assert(x <= more) by {
        // Since y >= 0, we have x <= x + y
        assert(x <= x + y);
    };
    assert(less <= x <= more);
    
    return (more, less);
}

}

The key changes made:

The verification works because:
- From `y >= 0` and `less = x - y`, we get `less <= x`
- From `y >= 0` and `more = x + y`, we get `x <= more`
- Therefore `less <= x <= more` holds