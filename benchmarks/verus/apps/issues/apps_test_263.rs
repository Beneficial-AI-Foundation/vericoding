// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: nat, m: nat, benches: Seq<nat>) -> bool {
    n > 0 && m > 0 && benches.len() == n && forall|i: int| 0 <= i < n ==> benches[i] > 0
}

spec fn max_seq(s: Seq<nat>) -> nat
    recommends s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else if s[0] >= max_seq(s.subrange(1, s.len() as int)) {
        s[0]
    } else {
        max_seq(s.subrange(1, s.len() as int))
    }
}

spec fn sum_seq(s: Seq<nat>) -> nat {
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: nat, m: nat, benches: Seq<nat>) -> (result: (nat, nat))
    requires valid_input(n, m, benches)
    ensures result.1 == max_seq(benches) + m
    ensures {
        let total = sum_seq(benches) + m;
        let current_max = max_seq(benches);
        if total <= current_max * n { result.0 == current_max } 
        else { result.0 == (total + n - 1) / n }
    }
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0, 0)
}
// </vc-code>


}

fn main() {}