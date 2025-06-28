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
    
    // Prove that the ensures clause holds
    assert(x + y == m + (s - m) == s);
    assert(x == m);
    assert(x <= m);
    
    // Prove that y <= m
    assert(y == s - m);
    assert(s <= 2 * m);  // from precondition
    assert(y <= m) by {
        assert(s <= 2 * m);
        assert(s - m <= 2 * m - m);
        assert(s - m <= m);
    };
    
    // The key insight: we need to ensure m == x || m == y
    // Since x = m, we have m == x, so the condition is satisfied
    assert(m == x);
    assert((m == x || m == y) && x <= m && y <= m);
    
    (x, y)
}

}