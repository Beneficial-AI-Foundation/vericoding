use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
            // Found a counterexample where a[i] <= b[i]
            assert(exists|k: int| 0 <= k < a.len() && a[k] <= b[k]) by {
                assert(0 <= i as int && i < a.len() && a[i as int] <= b[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    
    // If we've checked all elements and found no counterexample, 
    // then all elements of a are greater than corresponding elements of b
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] > b[j]);
    true
}
// </vc-code>

fn main() {}

}