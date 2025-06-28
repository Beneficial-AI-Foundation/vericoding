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