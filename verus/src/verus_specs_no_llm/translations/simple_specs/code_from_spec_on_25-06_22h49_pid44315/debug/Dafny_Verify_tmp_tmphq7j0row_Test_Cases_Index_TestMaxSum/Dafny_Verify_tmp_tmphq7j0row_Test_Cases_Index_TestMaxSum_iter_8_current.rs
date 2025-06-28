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
        assert(x + y <= y + y);  // Changed from < to <=
        assert(y + y == 2 * y);
        assert(s <= 2 * m);
    }
    
    let (reconstructed_a, reconstructed_b) = ReconstructFromMaxSum(s, m);
    
    // ReconstructFromMaxSum returns (m, s-m)
    assert(reconstructed_a == m);
    assert(reconstructed_b == s - m);
    assert(s == x + y);
    
    if x >= y {
        // When x >= y: m = x
        // reconstructed_a = m = x
        // reconstructed_b = s - m = (x + y) - x = y
        assert(m == x);
        assert(reconstructed_a == x);
        assert(reconstructed_b == (x + y) - x);
        assert(reconstructed_b == y);
        (reconstructed_a, reconstructed_b)
    } else {
        // When x < y: m = y
        // reconstructed_a = m = y  
        // reconstructed_b = s - m = (x + y) - y = x
        // We need to return (x, y), so we swap
        assert(m == y);
        assert(reconstructed_a == y);
        assert(reconstructed_b == (x + y) - y);
        assert(reconstructed_b == x);
        // Return (x, y) by swapping the reconstructed values
        (reconstructed_b, reconstructed_a)
    }
}

}