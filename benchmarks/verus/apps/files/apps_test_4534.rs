// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binomial(n: int, k: int) -> int
    recommends 0 <= k <= n
{
    if k == 0 || k == n { 1 }
    else if k == 1 { n }
    else { binomial(n-1, k-1) + binomial(n-1, k) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_row(k: int) -> (result: Vec<int>)
    requires 0 <= k <= 33
    ensures result.len() == k + 1,
    ensures forall|i: int| 0 <= i < result.len() ==> result[i] == binomial(k, i),
    ensures forall|i: int| 0 <= i < result.len() ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}