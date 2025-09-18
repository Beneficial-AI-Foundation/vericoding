// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): scalar NaN predicate */
spec fn is_nan_scalar(x: f64) -> bool { x != x }
// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct boolean mask indicating NaNs with correct invariant syntax */
    let mut result: Vec<bool> = Vec::new();
    let mut i: nat = 0;
    while i < x.len()
        invariant i <= x.len();
        invariant result.len() == i;
        invariant (forall |j: nat| j < i ==> result@[j] == (x@[j] != x@[j]));
        decreases x.len() - i;
    {
        result.push(is_nan_scalar(x@[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}