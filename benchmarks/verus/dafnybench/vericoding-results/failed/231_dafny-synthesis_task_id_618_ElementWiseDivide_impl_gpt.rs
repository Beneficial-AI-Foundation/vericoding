use vstd::prelude::*;

verus! {

// <vc-helpers>
pub open spec fn elt(a: Seq<int>, b: Seq<int>, i: int) -> int
    requires
        0 <= i < a.len(),
        a.len() == b.len(),
        0 <= i < b.len(),
        b[i] != 0
{
    a[i] / b[i]
}
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
{
    let res = Seq::new(a.len(), |i: int| elt(a, b, i));
    res
}
// </vc-code>

fn main() {
}

}