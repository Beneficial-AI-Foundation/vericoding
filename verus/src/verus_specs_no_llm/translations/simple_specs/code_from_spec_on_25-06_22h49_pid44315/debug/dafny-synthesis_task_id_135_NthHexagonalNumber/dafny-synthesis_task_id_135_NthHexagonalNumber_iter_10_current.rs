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
        // For n > 0, we know 2*n >= 2, so 2*n - 1 >= 1
        assert(n > 0);
        assert(2 * n >= 2);
        assert(2 * n - 1 >= 1);
        
        // Prove that 2*n fits in u32
        assert(n <= 46340);
        assert(2 * n <= 2 * 46340);
        assert(2 * 46340 == 92680);
        assert(2 * n <= 92680);
        assert(92680 < 0x100000000u64); // less than 2^32
        
        let temp = 2u32 * n;
        assert(temp >= 2);
        assert(temp == 2 * n);
        
        let temp2 = temp - 1u32;
        assert(temp2 == temp - 1);
        assert(temp2 == 2 * n - 1);
        
        // Prove that n * temp2 fits in u32
        assert(temp2 <= 2 * 46340 - 1);
        assert(temp2 <= 92679);
        assert(n * temp2 <= 46340 * 92679);
        assert(46340 * 92679 == 4294836060u64);
        assert(4294836060u64 < 0x100000000u64); // This is actually > 2^32, let me recalculate
        
        // Let me recalculate the bound more carefully
        assert(n <= 46340);
        assert(temp2 == 2 * n - 1);
        assert(temp2 <= 2 * 46340 - 1);
        assert(temp2 <= 92679);
        
        // For the maximum case: n = 46340, temp2 = 92679
        // n * temp2 = 46340 * 92679 = 4,294,836,060
        // But 2^32 = 4,294,967,296, so we're actually safe
        // Let me prove this step by step
        assert(n * temp2 <= 46340 * 92679);
        
        let result = n * temp2;
        
        // Proof that the computation matches the specification
        assert(result == n * temp2);
        assert(temp2 == 2 * n - 1);
        assert(result == n * (2 * n - 1));
        
        result
    }
}

}