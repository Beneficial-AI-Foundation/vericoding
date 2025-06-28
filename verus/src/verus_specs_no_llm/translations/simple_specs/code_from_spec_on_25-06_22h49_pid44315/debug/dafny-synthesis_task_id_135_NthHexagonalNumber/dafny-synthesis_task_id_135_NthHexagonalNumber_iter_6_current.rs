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
    let temp = 2u32.checked_mul(n).unwrap();
    let temp2 = temp.checked_sub(1u32).unwrap();
    let result = n.checked_mul(temp2).unwrap();
    
    // Proof that the computation matches the specification
    proof {
        assert(temp == 2 * n);
        assert(temp2 == temp - 1);
        assert(temp2 == 2 * n - 1);
        assert(result == n * temp2);
        assert(result == n * (2 * n - 1));
    }
    
    result
}

}