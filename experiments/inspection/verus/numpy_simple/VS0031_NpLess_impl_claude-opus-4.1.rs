// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple less-than helper for i8 */
fn lt_i8(a: i8, b: i8) -> bool { a < b }

// </vc-helpers>

// <vc-spec>
fn less(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (a@[i] < b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement elementwise comparison with invariant including length equality */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i as int ==> res@[j] == (a@[j] < b@[j]),
        decreases a.len() - i
    {
        let ai: i8 = a[i];
        let bi: i8 = b[i];
        res.push(ai < bi);
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}