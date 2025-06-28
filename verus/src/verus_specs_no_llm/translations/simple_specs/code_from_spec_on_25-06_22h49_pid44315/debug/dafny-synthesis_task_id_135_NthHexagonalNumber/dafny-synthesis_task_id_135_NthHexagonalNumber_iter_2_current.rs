use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthHexagonalNumber(n: u32) -> (hexNum: u32)
    requires
        n >= 0
    ensures
        hexNum == n * ((2 * n) - 1)
{
    n * (2 * n - 1)
}

}