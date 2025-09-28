// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn five(n: int) -> int { 5 * n }

proof fn bound_five_lt_5000(n: int)
    requires 0 <= n && n <= 999
    ensures five(n) <= 4995
{
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,

    ensures
        sum[0] == 5 * N,
// </vc-spec>
// <vc-code>
{
    assert(sum.len() == 1);
    proof {
        assert(0 < N@ && N@ < 1000);
        assert(5 * N@ <= 4995);
        assert(4995 <= i32::MAX@);
    }
    sum[0] = 5 * N;
}
// </vc-code>

}
fn main() {}