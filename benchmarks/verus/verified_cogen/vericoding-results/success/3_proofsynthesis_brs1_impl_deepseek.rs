// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Make lemma proof-only and ensure exec code doesn't call proof functions */
proof fn helper_lemma(v: &Vec<i32>, n: i32) 
    requires n > 0, v.len() == n
    ensures v@.len() == n
{
    assert(v@.len() == v.len() as nat);
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,

    ensures
        sum[0] <= N,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix compilation by removing proof function call from exec code */
{
    let len = a.len();
    proof {
        helper_lemma(a, N);
    }
    sum[0] = N;
}
// </vc-code>

}
fn main() {}