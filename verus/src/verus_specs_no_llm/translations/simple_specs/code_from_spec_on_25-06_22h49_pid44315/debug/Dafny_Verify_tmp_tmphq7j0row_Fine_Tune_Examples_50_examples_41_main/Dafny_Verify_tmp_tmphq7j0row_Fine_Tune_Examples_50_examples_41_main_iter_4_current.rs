use builtin::*;
use builtin_macros::*;

verus! {

fn main(n: int, k: int) -> (i: int, j: int)
    requires
        n >= 0,
        k == 1 || k >= 0
    ensures
        k + i + j >= 2 * n
{
    proof {
        // Both cases of the precondition guarantee k >= 0
        // Case 1: k == 1, so k >= 0
        // Case 2: k >= 0 directly
        // Therefore k >= 0 in both cases
        if k == 1 {
            assert(k >= 0);
        } else {
            assert(k >= 0); // from the second part of the OR
        }
        // With i = n and j = n, we get k + n + n = k + 2*n >= 2*n
        // since k >= 0
    }
    (n, n)
}

}

The key insight is that the precondition `k == 1 || k >= 0` actually means:
- Either `k == 1` (which implies `k >= 0` since `1 >= 0`)
- Or `k >= 0` directly

So in both cases, we have `k >= 0`. With the return values `i = n` and `j = n`, the postcondition becomes `k + n + n >= 2*n`, which simplifies to `k + 2*n >= 2*n`, and since `k >= 0`, this is always true.