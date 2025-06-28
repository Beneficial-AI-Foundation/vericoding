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
    let x = m;
    let y = s - m;
    (x, y)
}

fn TestMaxSum(x: int, y: int) -> (res_x: int, res_y: int)
    ensures res_x == x
    ensures res_y == y
{
    // Call MaxSum to get sum and max
    let (s, m) = MaxSum(x, y);
    
    // Prove s <= 2*m for the precondition of ReconstructFromMaxSum
    assert(s == x + y);
    assert(m == if x >= y { x } else { y });
    
    if x >= y {
        assert(m == x);
        assert(y <= x);
        assert(s == x + y);
        assert(x + y <= x + x);
        assert(x + x == 2 * x);
        assert(s <= 2 * m);
    } else {
        assert(m == y);
        assert(x < y);
        assert(s == x + y);
        assert(x + y < y + y);
        assert(y + y == 2 * y);
        assert(s <= 2 * m);
    }
    
    let (reconstructed_x, reconstructed_y) = ReconstructFromMaxSum(s, m);
    
    // Prove that we can reconstruct the original values correctly
    assert(reconstructed_x == m);
    assert(reconstructed_y == s - m);
    assert(s == x + y);
    
    if x >= y {
        // When x >= y: m = x, so reconstructed_x = m = x
        // and reconstructed_y = s - m = (x + y) - x = y
        assert(m == x);
        assert(reconstructed_x == x);
        assert(reconstructed_y == s - m);
        assert(reconstructed_y == (x + y) - x);
        assert(reconstructed_y == y);
        (reconstructed_x, reconstructed_y)
    } else {
        // When x < y: m = y, so reconstructed_x = m = y
        // and reconstructed_y = s - m = (x + y) - y = x
        // We need to swap to return (x, y)
        assert(m == y);
        assert(reconstructed_x == y);
        assert(reconstructed_y == s - m);
        assert(reconstructed_y == (x + y) - y);
        assert(reconstructed_y == x);
        (reconstructed_y, reconstructed_x)
    }
}

}