use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a == old(a),
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b.spec_index(i) == a.spec_index(a.len() - i - 1)
{
    let mut b = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            b.len() == i,
            forall|k: int| 0 <= k < i ==> b.spec_index(k) == a.spec_index(a.len() - 1 - k),
            a.len() > 0
    {
        // Add proof assertion to help with verification
        assert(0 <= a.len() - 1 - i < a.len());
        assert(a.len() - 1 - i == a.len() - i - 1);
        
        b.push(a[a.len() - 1 - i]);
        i = i + 1;
        
        // Proof block to establish the postcondition relationship
        assert forall|k: int| 0 <= k < i implies b.spec_index(k) == a.spec_index(a.len() - 1 - k) by {
            if k < i - 1 {
                // This follows from the loop invariant
            } else if k == i - 1 {
                // This is the element we just added
                assert(b.spec_index(k) == a.spec_index(a.len() - 1 - (i - 1)));
                assert(a.len() - 1 - (i - 1) == a.len() - 1 - k);
            }
        };
    }
    
    // Final proof to establish postcondition
    assert forall|i: int| 0 <= i < a.len() implies b.spec_index(i) == a.spec_index(a.len() - i - 1) by {
        // At loop exit, we have i == a.len(), so the loop invariant gives us:
        // forall|k: int| 0 <= k < a.len() ==> b.spec_index(k) == a.spec_index(a.len() - 1 - k)
        // We need to show this is equivalent to the postcondition
        assert(a.len() - 1 - i == a.len() - i - 1);
    };
    
    b
}

}