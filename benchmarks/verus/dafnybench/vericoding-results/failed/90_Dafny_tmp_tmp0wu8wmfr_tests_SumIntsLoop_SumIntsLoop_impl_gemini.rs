// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_ints(n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 {
        0
    } else {
        sum_ints(n - 1) + n
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed non-linear arithmetic syntax to be `by(nonlinear_arith)` */
proof fn sum_gauss_lemma(n: int)
    requires
        n >= 0
    ensures
        sum_ints(n) == n * (n + 1) / 2
    decreases n
{
    if n > 0 {
        sum_gauss_lemma(n - 1);
        assert(sum_ints(n) == sum_ints(n - 1) + n);
        assert((n - 1) * n / 2 + n == n * (n + 1) / 2) by(nonlinear_arith);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no changes required, logic is correct with the fixed helper */
{
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    while i < n
        invariant
            i <= n,
            s as int == sum_ints(i as int)
        decreases n - i
    {
        i = i + 1;
        s = s + i;
    }
    proof {
        sum_gauss_lemma(n as int);
    }
    s
}
// </vc-code>

}
fn main() {}