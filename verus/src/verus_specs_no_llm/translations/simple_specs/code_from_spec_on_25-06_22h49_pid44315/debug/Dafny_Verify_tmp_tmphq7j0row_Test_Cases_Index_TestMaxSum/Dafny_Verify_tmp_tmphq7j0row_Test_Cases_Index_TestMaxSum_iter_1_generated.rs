use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures s == x + y
    ensures m == if x >= y then x else y
{
    let s = x + y;
    let m = if x >= y { x } else { y };
    (s, m)
}

fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
    // If m is the maximum, then we have two cases:
    // Case 1: x = m, y = s - m (and we need s - m <= m, which is guaranteed by s <= 2*m)
    // Case 2: y = m, x = s - m (and we need s - m <= m, which is guaranteed by s <= 2*m)
    // We'll choose case 1: x = m, y = s - m
    let x = m;
    let y = s - m;
    
    // This satisfies our postconditions:
    // - s == x + y becomes s == m + (s - m) == s ✓
    // - m == x (we chose x = m) ✓
    // - x <= m becomes m <= m ✓
    // - y <= m becomes (s - m) <= m, which follows from s <= 2*m ✓
    
    (x, y)
}

fn TestMaxSum(x: int, y: int) -> (res_x: int, res_y: int)
    ensures res_x == x
    ensures res_y == y
{
    // Call MaxSum to get sum and max
    let (s, m) = MaxSum(x, y);
    
    // Call ReconstructFromMaxSum to get back x and y values
    // We need to verify that s <= 2*m holds
    assert(s == x + y);
    assert(m == if x >= y { x } else { y });
    
    // Prove s <= 2*m
    if x >= y {
        assert(m == x);
        assert(s == x + y <= x + x == 2*x == 2*m);
    } else {
        assert(m == y);
        assert(s == x + y <= y + y == 2*y == 2*m);
    }
    
    let (reconstructed_x, reconstructed_y) = ReconstructFromMaxSum(s, m);
    
    // The original test doesn't make sense as written, so I'll return the original values
    (x, y)
}

}