use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires 
        a.len() == b.len(),
    ensures 
        result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
        !result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i: int = 0int;
    while i < a.len() as int
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] > b[j],
    {
        if a[i] <= b[i] {
            proof {
                assert(exists|k: int| 0 <= k < a.len() && a[k] <= b[k]) by {
                    assert(0 <= i < a.len() && a[i] <= b[i]);
                }
            }
            return false;
        }
        i = i + 1int;
    }
    proof {
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] > b[j]);
        assert(!(exists|k: int| 0 <= k < a.len() && a[k] <= b[k])) by {
            if exists|k: int| 0 <= k < a.len() && a[k] <= b[k] {
                let k = choose|k: int| 0 <= k < a.len() && a[k] <= b[k];
                assert(a[k] > b[k]);
                assert(false);
            }
        }
    }
    true
}
// </vc-code>

fn main() {}

}