use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthHexagonalNumber(n: u32) -> (hexNum: u32)
    requires
        n <= 46340,  // Ensure no overflow: we need room for n * (2*n - 1)
    ensures
        hexNum == n * (2 * n - 1)
{
    if n == 0 {
        // Handle the n = 0 case explicitly
        assert(n * (2 * n - 1) == 0 * (2 * 0 - 1));
        assert(0 * (2 * 0 - 1) == 0);
        0
    } else {
        let temp = 2u32 * n;
        let temp2 = temp - 1u32;
        let result = n * temp2;
        
        // Proof that the computation matches the specification
        assert(temp == 2 * n);
        assert(temp2 == temp - 1);
        assert(temp2 == 2 * n - 1);
        assert(result == n * temp2);
        assert(result == n * (2 * n - 1));
        
        result
    }
}

}