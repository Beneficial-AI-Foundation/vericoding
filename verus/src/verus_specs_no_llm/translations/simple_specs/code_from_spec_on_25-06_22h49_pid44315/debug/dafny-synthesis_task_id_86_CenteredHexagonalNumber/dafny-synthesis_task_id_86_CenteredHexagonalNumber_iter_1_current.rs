use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CenteredHexagonalNumber(n: nat) -> (result: nat)
    requires
        n >= 0
    ensures
        result == 3 * n * (n - 1) + 1
{
    3 * n * (n - 1) + 1
}

}

The implementation directly computes the mathematical formula specified in the postcondition. Since `n` is of type `nat` (natural number), it's guaranteed to be non-negative, which satisfies the precondition. The computation `3 * n * (n - 1) + 1` will always produce a natural number result, and Verus should be able to verify that this matches the postcondition exactly.