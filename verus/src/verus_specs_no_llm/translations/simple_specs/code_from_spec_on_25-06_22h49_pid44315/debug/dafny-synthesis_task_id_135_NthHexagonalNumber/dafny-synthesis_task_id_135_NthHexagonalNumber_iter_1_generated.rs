// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthHexagonalNumber(n: int) -> (hexNum: int)
    requires
        n >= 0
    ensures
        hexNum == n * ((2 * n) - 1)
{
    n * (2 * n - 1)
}

}