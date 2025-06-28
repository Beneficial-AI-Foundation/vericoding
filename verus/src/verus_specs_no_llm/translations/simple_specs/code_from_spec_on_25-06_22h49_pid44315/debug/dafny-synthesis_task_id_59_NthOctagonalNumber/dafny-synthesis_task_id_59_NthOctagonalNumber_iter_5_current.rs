use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthOctagonalNumber(n: u32) -> (octagonalNumber: u32)
    requires
        n >= 0,
        n <= 18918, // Ensures no overflow: n * (3 * n - 2) <= u32::MAX
    ensures
        octagonalNumber == n * (3 * n - 2)
{
    let three_n = 3 * n;
    let three_n_minus_2 = three_n - 2;
    let result = n * three_n_minus_2;
    
    proof {
        // Prove that the arithmetic doesn't overflow
        assert(n <= 18918);
        assert(3 * n <= 3 * 18918);
        assert(3 * n - 2 <= 3 * 18918);
        assert(n * (3 * n - 2) <= 18918 * (3 * 18918));
    }
    
    result
}

}