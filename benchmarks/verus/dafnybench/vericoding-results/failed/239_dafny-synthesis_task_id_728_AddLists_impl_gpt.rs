use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn add_lists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    Seq::new(a.len(), |i: int| a[i] + b[i])
}
// </vc-code>

fn main() {}

}