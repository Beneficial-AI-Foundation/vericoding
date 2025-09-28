use vstd::prelude::*;

verus! {

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
    let res = forall|i: int| 0 <= i && i < a.len() ==> a[i] > b[i];
    if !res {
        assert(exists|i: int| 0 <= i && i < a.len() && a[i] <= b[i]);
    } else {
        assert(forall|i: int| 0 <= i && i < a.len() ==> a[i] > b[i]);
    }
    res
}
// </vc-code>

fn main() {}

}