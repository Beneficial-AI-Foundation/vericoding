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
    // Add explicit reasoning that k >= 0 implies k + 2*n >= 2*n
    assert(k >= 0);
    assert(k + 2 * n >= 0 + 2 * n) by {
        // Since k >= 0, adding k to 2*n gives us at least 2*n
    };
    assert(0 + 2 * n == 2 * n);
    assert(k + 2 * n >= 2 * n);
    result
}

}