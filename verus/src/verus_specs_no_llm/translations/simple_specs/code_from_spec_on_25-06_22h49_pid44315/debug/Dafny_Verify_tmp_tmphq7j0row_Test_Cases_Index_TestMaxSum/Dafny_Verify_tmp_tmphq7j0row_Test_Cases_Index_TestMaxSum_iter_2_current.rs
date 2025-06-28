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
        assert(s == x + y);
        assert(y <= x); // since x >= y
        assert(s == x + y <= x + x);
        assert(2 * x == 2 * m);
        assert(s <= 2 * m);
    } else {
        assert(m == y);
        assert(s == x + y);
        assert(x < y); // since !(x >= y)
        assert(x <= y);
        assert(s == x + y <= y + y);
        assert(2 * y == 2 * m);
        assert(s <= 2 * m);
    }
    
    let (reconstructed_x, reconstructed_y) = ReconstructFromMaxSum(s, m);
    
    // Now we need to prove that the reconstructed values equal the original values
    // From ReconstructFromMaxSum: reconstructed_x = m, reconstructed_y = s - m
    // We need to show this equals (x, y)
    
    proof {
        if x >= y {
            // m == x, so reconstructed_x = m = x
            // reconstructed_y = s - m = (x + y) - x = y
            assert(m == x);
            assert(reconstructed_x == m);
            assert(reconstructed_x == x);
            assert(reconstructed_y == s - m);
            assert(reconstructed_y == (x + y) - x);
            assert(reconstructed_y == y);
        } else {
            // m == y, so we need to show that m = x and s - m = y
            // But this is not generally true! We have a problem with the reconstruction.
            // The issue is that ReconstructFromMaxSum always returns (m, s-m)
            // but we need it to return the original (x, y) which could be (x, y) or (y, x)
            
            // Since m == y and we want to return (x, y), but reconstruction gives (m, s-m) = (y, x)
            // We need to swap them back
            assert(m == y);
            assert(reconstructed_x == m);
            assert(reconstructed_x == y);
            assert(reconstructed_y == s - m);
            assert(reconstructed_y == (x + y) - y);
            assert(reconstructed_y == x);
        }
    }
    
    // We need to return the values in the correct order
    if x >= y {
        (reconstructed_x, reconstructed_y)
    } else {
        // Swap back since reconstruction returned (y, x) but we need (x, y)
        (reconstructed_y, reconstructed_x)
    }
}

}