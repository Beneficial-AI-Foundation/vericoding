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
    let result = (n, n);
    assert(k + result.0 + result.1 == k + n + n);
    assert(k + n + n == k + 2 * n);
    assert(k >= 0 && k + 2 * n >= 2 * n);
    result
}

}