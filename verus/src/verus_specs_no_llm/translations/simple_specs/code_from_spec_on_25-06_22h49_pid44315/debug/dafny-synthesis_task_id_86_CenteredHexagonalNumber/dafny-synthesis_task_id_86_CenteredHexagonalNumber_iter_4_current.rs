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