// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_division(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using an exec 'usize' counter and an exec 'Vec' */
    let mut result: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b[k] != 0,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result.view()@[j] == a@[j] / b@[j],
        decreases a.len() - i
    {
        let val = a@[i as int] / b@[i as int];
        result.push(val);
        i = i + 1;
    }
    result.view()
}
// </vc-code>

}
fn main() {}