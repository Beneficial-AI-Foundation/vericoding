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
pub proof fn lemma_tri_step(i: int)
    requires
        0 <= i,
    ensures
        i * (i - 1) / 2 + i == (i + 1) * i / 2,
{
}

pub proof fn lemma_max_sum_closed_form(n: int)
    requires
        n >= 0,
    ensures
        max_sum(n) == n * (n - 1) / 2,
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
{
    let nn: int = n as int;
    let mut i: int = 0;
    let mut s: int = 0;
    while i < nn
        invariant
            0 <= i,
            i <= nn,
            s == i * (i - 1) / 2,
        decreases nn - i
    {
        proof {
            lemma_tri_step(i);
        }
        s = s + i;
        i = i + 1;
    }
    let result: i8 = s as i8;
    result
}
// </vc-code>


}

fn main() {}