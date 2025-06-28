use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSmaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires
        a.len() == b.len()
    ensures
        result <==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) > b.spec_index(i),
        !result <==> exists i :: 0 <= i < a.len() && a.spec_index(i) <= b.spec_index(i)
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall j :: 0 <= j < i ==> a.spec_index(j) > b.spec_index(j)
    {
        if a.spec_index(i as int) <= b.spec_index(i as int) {
            // Prove the second postcondition
            assert(exists k :: 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k)) by {
                assert(0 <= i < a.len());
                assert(a.spec_index(i as int) <= b.spec_index(i as int));
            };
            return false;
        }
        i = i + 1;
    }
    
    // When we exit the loop, we've checked all elements
    assert(i == a.len());
    assert(forall j :: 0 <= j < a.len() ==> a.spec_index(j) > b.spec_index(j)) by {
        // The loop invariant gives us this property for all j < i
        // and i == a.len(), so we have it for all valid indices
    };
    
    // Prove the second postcondition (negation)
    assert(!(exists k :: 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k))) by {
        // Since we proved forall j, a[j] > b[j], there cannot exist any k with a[k] <= b[k]
        if exists k :: 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k) {
            // This would contradict our forall statement
            let k_witness = choose |k| 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k);
            assert(a.spec_index(k_witness) > b.spec_index(k_witness)); // from forall
            assert(a.spec_index(k_witness) <= b.spec_index(k_witness)); // from exists
            assert(false); // contradiction
        }
    };
    
    return true;
}

}