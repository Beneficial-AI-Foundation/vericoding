// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_divide(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replaced spec function Seq::new with an exec loop to build the result vector */
{
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result@.index(j) == a.index(j) / b.index(j),
            forall|k: int| 0 <= k < b.len() ==> b.index(k) != 0,
        decreases a.len() - i
    {
        assert(b[i] != 0);
        let val = a[i] / b[i];
        result.push(val);
        i = i + 1;
    }
    result.seq()
}
// </vc-code>

}
fn main() {}