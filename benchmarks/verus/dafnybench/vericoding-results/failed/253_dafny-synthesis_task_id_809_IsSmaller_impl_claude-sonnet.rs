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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] > b[j],
    {
        if a[i as int] <= b[i as int] {
            assert(exists|k: int| 0 <= k < a.len() && a[k] <= b[k]) by {
                assert(0 <= i < a.len());
                assert(a[i as int] <= b[i as int]);
            }
            return false;
        }
        i += 1;
    }
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] > b[j]);
    true
}
// </vc-code>

fn main() {}

}