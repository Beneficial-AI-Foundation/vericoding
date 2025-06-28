use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthHexagonalNumber(n: u32) -> (hexNum: u32)
    requires
        n >= 0,
        n <= 46340,  // Ensure no overflow: sqrt(u32::MAX) ≈ 65535, but we need room for (2*n-1)
    ensures
        hexNum == n * ((2 * n) - 1)
{
    let temp = 2 * n;
    let temp2 = temp - 1;
    n * temp2
}

}