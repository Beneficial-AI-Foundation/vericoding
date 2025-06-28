use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthOctagonalNumber(n: u32) -> (octagonalNumber: u32)
    requires
        n <= 18918, // Ensures no overflow: n * (3 * n - 2) <= u32::MAX
    ensures
        octagonalNumber == n * (3 * n - 2)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        // Compute n * (3 * n - 2) as n * 3 * n - n * 2 to avoid intermediate overflow
        // This is equivalent to 3 * n * n - 2 * n
        let n_squared = n * n;
        let three_n_squared = 3 * n_squared;
        let two_n = 2 * n;
        let result = three_n_squared - two_n;
        
        proof {
            // Prove the arithmetic equivalence and bounds
            assert(n >= 2);
            assert(n <= 18918);
            
            // Show that n * (3 * n - 2) == 3 * n * n - 2 * n
            assert(n * (3 * n - 2) == n * 3 * n - n * 2) by {
                assert(n * (3 * n - 2) == n * (3 * n) - n * 2);
                assert(n * (3 * n) == n * 3 * n);
            }
            
            // The computation is equivalent to our result
            assert(result == 3 * n * n - 2 * n);
            assert(3 * n * n - 2 * n == n * (3 * n - 2));
        }
        
        result
    }
}

}