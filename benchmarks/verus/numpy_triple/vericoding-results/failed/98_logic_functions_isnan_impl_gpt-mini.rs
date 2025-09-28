// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): boolean exhaustiveness proof */
fn bool_total(b: bool)
    ensures
        b == true || b == false,
{
    proof {
        if b {
            assert(b == true || b == false);
        } else {
            assert(b == true || b == false);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push is_nan flags */
    let n: int = x@.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            (res.len() as int) == i,
            forall|j: int| 0 <= j < i ==> res[j as usize] == (x@[j] != x@[j]),
            0 <= i <= n,
        decreases
            n - i
    {
        let xi: f64 = x[i as usize];
        res.push(xi != xi);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}