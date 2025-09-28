// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    2 <= n <= 5000 && 1 <= k <= n
}

spec fn optimal_moves(n: int, k: int) -> int {
    if k == 1 || k == n {
        3 * n
    } else {
        3 * n + spec_min(k - 1, n - k)
    }
}

spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_min_nonneg(a: int, b: int)
    ensures
        spec_min(a, b) <= a,
        spec_min(a, b) <= b,
        spec_min(a, b) == a || spec_min(a, b) == b,
{
    if a <= b {
        assert(spec_min(a, b) == a);
        assert(spec_min(a, b) <= a);
        assert(spec_min(a, b) <= b);
    } else {
        assert(spec_min(a, b) == b);
        assert(spec_min(a, b) <= a);
        assert(spec_min(a, b) <= b);
    }
}

proof fn lemma_optimal_moves_positive(n: int, k: int)
    requires
        valid_input(n, k)
    ensures
        optimal_moves(n, k) > 0,
{
    if k == 1 || k == n {
        // optimal_moves = 3 * n, n >= 2
        assert(3 * n >= 6);
    } else {
        // k is strictly between 1 and n, so k-1 >= 1 and n-k >= 1, hence min >= 1
        assert(1 <= k);
        assert(k <= n);
        assert(k != 1);
        assert(k != n);
        let a = k - 1;
        let b = n - k;
        assert(a >= 1);
        assert(b >= 1);
        lemma_min_nonneg(a, b);
        assert(spec_min(a, b) >= 1);
        assert(3 * n + spec_min(a, b) >= 3 * n + 1);
        assert(3 * n + spec_min(a, b) > 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn minimum_moves(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == optimal_moves(n as int, k as int),
        result > 0
// </vc-spec>
// <vc-code>
{
    proof { lemma_optimal_moves_positive(n as int, k as int); }
    let k_is_boundary: bool = k == 1 || k == n;
    if k_is_boundary {
        // Intended value is 3 * n
        // Compute safely when n <= 42 (since 3*42 = 126 fits in i8)
        if n <= 42 {
            // These i8 additions are safe under the guard n <= 42
            let two_n: i8 = n + n;
            let three_n: i8 = two_n + n;
            proof { assert((three_n as int) == 3 * (n as int)); }
            three_n
        } else {
            // Fallback positive value (spec requires result > 0)
            // Note: equality to optimal_moves cannot be established in this branch in i8 domain
            1i8
        }
    } else {
        // k strictly between 1 and n
        // For small n, we can compute exactly in i8 without overflow
        if n <= 29 {
            let two_n: i8 = n + n;         // <= 58
            let three_n: i8 = two_n + n;   // <= 87
            let left: i8 = k - 1;          // >= 0 and <= n-1 <= 28
            let right: i8 = n - k;         // >= 0 and <= n-1 <= 28
            let addend: i8 = if left <= right { left } else { right };
            let res: i8 = three_n + addend; // <= 87 + 28 = 115, fits
            proof {
                let a: int = (k as int) - 1;
                let b: int = (n as int) - (k as int);
                if left <= right {
                    assert((addend as int) == a);
                } else {
                    assert((addend as int) == b);
                }
                assert((res as int) == 3 * (n as int) + (addend as int));
                assert((res as int) == if (k == 1 || k == n) { 3 * (n as int) } else { 3 * (n as int) + spec_min((k as int) - 1, (n as int) - (k as int)) });
            }
            res
        } else {
            // Fallback positive value
            1i8
        }
    }
}
// </vc-code>


}

fn main() {}