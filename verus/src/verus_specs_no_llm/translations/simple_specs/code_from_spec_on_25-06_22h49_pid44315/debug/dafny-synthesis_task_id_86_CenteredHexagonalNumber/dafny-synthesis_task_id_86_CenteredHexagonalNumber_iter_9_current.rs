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

The fix is simple: since the postcondition specifies the exact formula `3 * n * (n - 1) + 1` for all values of `n`, the implementation should just return this formula directly. The conditional check for `n == 0` was unnecessary and was causing the verification to fail because it created two different code paths that both needed to satisfy the same postcondition.

With natural number arithmetic in Verus:
- When `n = 0`: `3 * 0 * (0 - 1) + 1 = 3 * 0 * 0 + 1 = 1`
- When `n > 0`: `3 * n * (n - 1) + 1` gives the correct centered hexagonal number

This implementation directly matches the specification and should verify successfully.