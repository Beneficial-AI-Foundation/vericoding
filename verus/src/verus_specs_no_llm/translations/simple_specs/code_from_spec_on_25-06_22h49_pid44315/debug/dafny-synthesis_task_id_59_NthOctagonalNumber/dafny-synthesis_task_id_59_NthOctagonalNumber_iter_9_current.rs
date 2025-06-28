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
        // Compute n * (3 * n - 2) directly with proper bounds checking
        let three_n = 3 * n;
        let three_n_minus_2 = three_n - 2;
        let result = n * three_n_minus_2;
        
        proof {
            // Prove the arithmetic equivalence
            assert(n >= 2);
            assert(n <= 18918);
            
            // Show that our computation is correct
            assert(three_n == 3 * n);
            assert(three_n_minus_2 == 3 * n - 2);
            assert(result == n * (3 * n - 2));
        }
        
        result
    }
}

}