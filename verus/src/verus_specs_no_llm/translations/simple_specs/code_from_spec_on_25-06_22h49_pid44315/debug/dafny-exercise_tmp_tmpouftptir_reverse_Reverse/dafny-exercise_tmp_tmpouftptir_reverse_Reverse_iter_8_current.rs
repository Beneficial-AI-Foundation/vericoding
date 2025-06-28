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
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            b.len() == i,
            forall|k: int| 0 <= k < i ==> b.spec_index(k) == a.spec_index(a.len() - k - 1),
            a.len() > 0
    {
        let src_index = a.len() - 1 - i;
        
        // Key assertions to help verification
        assert(i < a.len());
        assert(src_index < a.len());
        assert(src_index == a.len() - 1 - i);
        
        b.push(a[src_index]);
        
        // Critical proof block to establish the invariant after push
        proof {
            let new_len = i + 1;
            assert(b.len() == new_len);
            
            // The newly added element at position i
            assert(b.spec_index(i as int) == a.spec_index(src_index as int));
            assert(src_index as int == a.len() - 1 - i as int);
            assert(b.spec_index(i as int) == a.spec_index(a.len() - (i as int) - 1));
            
            // All previous elements still satisfy the invariant
            assert forall|k: int| 0 <= k < i ==> b.spec_index(k) == a.spec_index(a.len() - k - 1) by {
                // This follows from the loop invariant before the iteration
            };
            
            // Combined: all elements from 0 to i (inclusive) satisfy the invariant
            assert forall|k: int| 0 <= k < new_len ==> b.spec_index(k) == a.spec_index(a.len() - k - 1) by {
                if k < i {
                    // Previous elements - already established
                } else if k == i {
                    // Newly added element - established above
                }
            };
        }
        
        i = i + 1;
    }
    
    // After the loop, prove the postcondition
    proof {
        assert(i == a.len());
        assert(b.len() == a.len());
        assert forall|k: int| 0 <= k < a.len() ==> b.spec_index(k) == a.spec_index(a.len() - k - 1) by {
            // This follows directly from the loop invariant
        };
    }
    
    b
}

}