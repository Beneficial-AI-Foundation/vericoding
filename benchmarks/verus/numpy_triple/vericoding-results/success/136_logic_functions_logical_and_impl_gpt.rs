// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define sequence-level logical_and for specs */
pub open spec fn logical_and_seq(x1: Seq<bool>, x2: Seq<bool>) -> Seq<bool>
    recommends
        x1.len() == x2.len(),
{
    Seq::new(x1.len(), |i: int| x1[i] && x2[i])
}

// </vc-helpers>

// <vc-spec>
fn numpy_logical_and(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] && x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement element-wise logical_and using a loop and invariants (avoid from_seq) */
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            0 <= i as int <= n as int,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1@[j] && x2@[j]),
        decreases (n as int) - (i as int)
    {
        let b = x1[i] && x2[i];
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}