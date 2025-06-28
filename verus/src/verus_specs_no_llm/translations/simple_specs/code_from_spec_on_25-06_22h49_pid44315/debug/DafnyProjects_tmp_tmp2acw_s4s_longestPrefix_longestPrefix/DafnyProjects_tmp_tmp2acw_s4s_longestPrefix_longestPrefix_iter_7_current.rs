use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longestPrefix(a: &[int], b: &[int]) -> (i: usize)
    ensures
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i] != b[i]
{
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len()
        invariant
            i <= a.len() && i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
            forall|j: int| 0 <= j < i ==> a[j] == b[j]
    {
        if a[i] != b[i] {
            // At this point we know a[i] != b[i], so we can return i
            // The postcondition will be satisfied
            proof {
                // The subrange equality holds by the loop invariant
                assert(a@.subrange(0, i as int) == b@.subrange(0, i as int));
                // We have i < a.len() && i < b.len() && a[i] != b[i]
                assert(i < a.len() && i < b.len() && a[i] != b[i]);
            }
            return i;
        }
        
        proof {
            // After checking a[i] == b[i], we can extend the subrange equality
            assert(a[i] == b[i]);
            let old_i = i;
            assert(a@.subrange(0, old_i as int) == b@.subrange(0, old_i as int));
        }
        
        i = i + 1;
        
        proof {
            // Prove the subrange equality for the new i
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int)) by {
                let prev_i = (i - 1) as int;
                assert(a@.subrange(0, prev_i) == b@.subrange(0, prev_i));
                assert(a[prev_i] == b[prev_i]);
            }
        }
    }
    
    // If we exit the loop, it means i >= a.len() || i >= b.len()
    // In this case, the third postcondition is vacuously true
    proof {
        assert(i >= a.len() || i >= b.len());
        assert(!(i < a.len() && i < b.len()));
        // The implication i < a.len() && i < b.len() ==> a[i] != b[i] is vacuously true
    }
    
    i
}

}