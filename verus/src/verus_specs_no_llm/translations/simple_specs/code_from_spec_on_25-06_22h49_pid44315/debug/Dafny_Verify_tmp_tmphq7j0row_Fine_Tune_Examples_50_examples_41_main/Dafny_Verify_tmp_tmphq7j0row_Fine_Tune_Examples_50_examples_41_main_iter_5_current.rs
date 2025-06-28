use builtin::*;
use builtin_macros::*;

verus! {

fn main(n: int, k: int) -> (i: int, j: int)
    requires
        n >= 0,
        k >= 0
    ensures
        k + i + j >= 2 * n
{
    (n, n)
}

}