use vstd::prelude::*;

verus! {

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
    Seq::new(a.len(), |i: int| {
        assert(0 <= i && i < a.len());
        assert(a.len() == b.len());
        assert(0 <= i && i < b.len());
        assert(b[i] != 0);
        a[i] / b[i]
    })
}
// </vc-code>

fn main() {
}

}