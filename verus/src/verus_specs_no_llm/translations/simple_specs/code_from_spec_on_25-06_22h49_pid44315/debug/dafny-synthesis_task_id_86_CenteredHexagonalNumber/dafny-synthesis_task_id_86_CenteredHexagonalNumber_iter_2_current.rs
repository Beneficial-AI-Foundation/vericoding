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
    if n == 0 {
        1
    } else {
        3 * n * (n - 1) + 1
    }
}

}