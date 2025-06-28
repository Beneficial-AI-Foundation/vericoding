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
        assert(s - m <= m);
    };
    
    (x, y)
}

}