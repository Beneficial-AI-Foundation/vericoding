use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CenteredHexagonalNumber(n: nat) -> (result: nat)
    ensures
        result == 3 * n * (n - 1) + 1
{
    3 * n * (n - 1) + 1
}

}

The fix simplifies the function by removing the unnecessary conditional branch. Since the formula `3 * n * (n - 1) + 1` works correctly for all natural numbers including 0 (due to natural number arithmetic where `0 - 1 = 0`), we can use it directly without special casing.