use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthDecagonalNumber(n: int) -> (decagonal: int)
    requires
        n >= 0
    ensures
        decagonal == 4 * n * n - 3 * n
{
    4 * n * n - 3 * n
}

}

The implementation directly computes `4 * n * n - 3 * n` and returns it. Since this exactly matches the postcondition `decagonal == 4 * n * n - 3 * n`, Verus can automatically verify that the implementation satisfies the specification.