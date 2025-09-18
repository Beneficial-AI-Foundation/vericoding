// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): f64 zero predicate */
spec fn f64_is_zero(x: f64) -> bool { x == 0.0 }
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement logical_not with loop and simple invariants */
    let n: nat = x.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n,
        invariant res.len() == i,
        decreases n - i
    {
        let xi = x[i];
        res.push(xi == 0.0);
        i = i + 1;
    }
    result = res;
}
// </vc-code>

}
fn main() {}