use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires
        s <= 2 * m
    ensures
        s == (x + y),
        (m == x || m == y) && x <= m && y <= m
{
    // Given s <= 2*m, we have s - m <= m, so we can always use the first branch
    let x = m;
    let y = s - m;
    
    // Prove that y <= m
    assert(y == s - m);
    assert(s <= 2 * m);  // from precondition
    assert(y <= m) by {
        // From s <= 2*m, we get s - m <= m
        assert(s <= 2 * m);
        assert(s - m <= 2 * m - m);
        assert(s - m <= m);
        assert(y == s - m);
    };
    
    (x, y)
}

}