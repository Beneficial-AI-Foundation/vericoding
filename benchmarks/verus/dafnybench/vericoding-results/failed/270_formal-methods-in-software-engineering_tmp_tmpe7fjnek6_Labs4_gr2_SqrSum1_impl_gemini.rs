// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sqr_sum_rec(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 { 0 } else { n*n + sqr_sum_rec(n-1) }
}

proof fn l1(n: int)
    requires n >= 0
    ensures sqr_sum_rec(n) == n*(n+1)*(2*n + 1)/6
    decreases n
{

}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change from previous turn */
proof fn sqr_sum_rec_lemma(n: int)
    requires
        n > 0,
    ensures
        sqr_sum_rec(n) == n * n + sqr_sum_rec(n - 1),
{
}
// </vc-helpers>

// <vc-spec>
fn sqr_sum1(n: int) -> (s: int)
    requires n >= 0
    ensures s == sqr_sum_rec(n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): wrap logic in a proof block to allow ghost variables */
    proof {
        let mut s: int = 0;
        let mut i: int = 1;
        while i <= n
            invariant
                n >= 0,
                1 <= i <= n + 1,
                s == sqr_sum_rec(i - 1),
            decreases n - i
        {
            sqr_sum_rec_lemma(i);
            s = s + i * i;
            i = i + 1;
        }
        return s;
    }
}
// </vc-code>

}
fn main() {}