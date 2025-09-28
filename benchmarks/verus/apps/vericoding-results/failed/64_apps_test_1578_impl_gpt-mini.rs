// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_sum(n: int) -> int
    recommends n >= 1
{
    n * (n - 1) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): specify decreases literal type */
spec fn lemma_acc_step(i: int, acc: int) -> ()
    requires
        acc == i*(i-1)/2,
    ensures
        acc + i == (i+1)*i/2,
    decreases
        0::<nat>
{
    proof {
        assert(acc + i == (i*(i-1)/2) + i);
        assert((i*(i-1) + 2*i)/2 == (i*(i+1))/2);
        assert((i*(i+1))/2 == (i+1)*i/2);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute sum of 0..n-1 using loop and lemma */
{
    let mut i: i64 = 0i64;
    let mut acc: i64 = 0i64;
    let n_i64: i64 = n as i64;
    while i < n_i64
        invariant
            0 <= i as int && i as int <= n as int,
            acc as int == (i as int)*(i as int - 1)/2,
        decreases
            (n as int - i as int) as nat
    {
        proof {
            lemma_acc_step(i as int, acc as int);
        }
        acc = acc + i;
        i = i + 1;
    }
    let res_i8: i8 = acc as i8;
    res_i8
}

// </vc-code>


}

fn main() {}