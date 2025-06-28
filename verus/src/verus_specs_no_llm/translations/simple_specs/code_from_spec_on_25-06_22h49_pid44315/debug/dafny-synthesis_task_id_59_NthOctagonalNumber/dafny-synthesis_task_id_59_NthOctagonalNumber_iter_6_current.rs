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
    if n < 2 {
        // For n = 0: 0 * (0 - 2) = 0 * (-2) = 0
        // For n = 1: 1 * (3 - 2) = 1 * 1 = 1
        // But we need to handle underflow for n * (3 * n - 2)
        if n == 0 {
            0
        } else { // n == 1
            1
        }
    } else {
        let three_n = 3 * n;
        let three_n_minus_2 = three_n - 2;
        let result = n * three_n_minus_2;
        
        proof {
            // Prove that the arithmetic doesn't overflow
            assert(n >= 2);
            assert(n <= 18918);
            assert(3 * n >= 6);
            assert(3 * n - 2 >= 4);
            assert(n * (3 * n - 2) <= 18918 * (3 * 18918 - 2));
        }
        
        result
    }
}

}