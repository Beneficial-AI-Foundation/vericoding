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
        // Since k == 1 || k >= 0, we have k >= 0
        // With i = n and j = n, we get k + n + n = k + 2*n >= 2*n
        assert(k >= 0);
    }
    (n, n)
}

}

The proof annotation helps Verus understand that since `k >= 0` (from the precondition), and we're returning `i = n` and `j = n`, the postcondition `k + i + j >= 2 * n` becomes `k + n + n >= 2 * n`, which simplifies to `k + 2*n >= 2*n`, which is equivalent to `k >= 0`, which is guaranteed by our precondition.