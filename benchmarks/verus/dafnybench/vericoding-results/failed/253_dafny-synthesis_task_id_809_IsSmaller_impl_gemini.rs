// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires 
        a.len() == b.len(),
    ensures 
        result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
        !result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The function has ghost parameters (Seq<int>), so it cannot have an executable body that inspects them. This implementation provides a ghost-level conditional that is equivalent to the spec. */
    if forall|i: int| 0 <= i < a.len() ==> a[i] > b[i] {
        true
    } else {
        false
    }
}
// </vc-code>

}
fn main() {}