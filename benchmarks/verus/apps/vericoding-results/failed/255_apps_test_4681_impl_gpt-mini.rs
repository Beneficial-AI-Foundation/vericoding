// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn lucas(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        2
    } else if n == 1 {
        1
    } else {
        lucas(n - 1) + lucas(n - 2)
    }
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 86
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof of Lucas recurrence for m>=2 */
proof fn lucas_recur(m: int)
    requires m >= 2
    ensures lucas(m) == lucas(m - 1) + lucas(m - 2),
    decreases m
{
    if m == 2 {
        assert(lucas(2) == lucas(1) + lucas(0));
    } else {
        lucas_recur(m - 1);
        assert(lucas(m) == lucas(m - 1) + lucas(m - 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == lucas(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative lucas computation using tracked ghost variables to relate runtime values to spec */
    let N: int = tracked(n as int);
    // runtime variables
    let mut a_r: i8 = 2;
    let mut b_r: i8 = 1;
    let mut k_r: i8 = 2;
    // tracked ghost mirrors
    let mut a: int = tracked(2);
    let mut b: int = tracked(1);
    let mut k: int = tracked(2);
    // initial proofs of invariants
    proof {
        assert(a == lucas(k - 2));
        assert(b == lucas(k - 1));
        assert(a_r as int == a);
        assert(b_r as int == b);
        assert(k_r as int == k);
    }
    while k_r <= n
        invariant
            2 <= k <= N + 1,
            a == lucas(k - 2),
            b == lucas(k - 1),
            a_r as int == a,
            b_r as int == b,
            k_r as int == k,
        decreases N - k
    {
        let c_r: i8 = a_r + b_r;
        let c: int = tracked(a + b);
        proof {
            lucas_recur(k);
            assert(c == lucas(k));
            assert(c == a + b);
        }
        a_r = b_r;
        b_r = c_r;
        k_r = k_r + 1;
        a = b;
        b = c;
        k = k + 1;
    }
    proof {
        assert(k == N + 1);
        assert(b == lucas(N));
        assert(b_r as int == b);
    }
    b_r
}
// </vc-code>


}

fn main() {}