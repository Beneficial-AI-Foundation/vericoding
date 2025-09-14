// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate asserting the input slice is non-decreasing */
spec fn is_nondec(a: &[i32]) -> bool { forall|i: int, j: int| 0 <= i && i < j && j < a.len() ==> a[i] <= a[j] }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use usize indices and Vec indexing; maintain strict-increasing invariant on res@ */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|p: int, q: int|
                0 <= p && p < q && q < (res.len() as int) ==> res@[p] < res@[q],
        decreases
            a.len() - i
    {
        if res.len() == 0 {
            res.push(a[i]);
        } else {
            let last = res[res.len() - 1];
            if a[i] > last {
                res.push(a[i]);
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}