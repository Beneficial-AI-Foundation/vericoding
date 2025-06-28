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
    let x = m;
    let y = s - m;
    
    // Prove that y <= m using the precondition
    assert(y <= m) by {
        assert(y == s - m);
        assert(s <= 2 * m);
        // From s <= 2*m, we get s - m <= 2*m - m, which is s - m <= m
        assert(s - m <= 2 * m - m);
        assert(2 * m - m == m);
        assert(s - m <= m);
        assert(y <= m);
    };
    
    (x, y)
}

}