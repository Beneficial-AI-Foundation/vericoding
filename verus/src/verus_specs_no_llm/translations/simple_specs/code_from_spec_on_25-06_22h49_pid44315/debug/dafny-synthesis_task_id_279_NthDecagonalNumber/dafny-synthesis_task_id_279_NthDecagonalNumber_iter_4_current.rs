use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn NthDecagonalNumber(n: int) -> int
    requires
        n >= 0
    ensures
        NthDecagonalNumber(n) == 4 * n * n - 3 * n
{
    4 * n * n - 3 * n
}

}