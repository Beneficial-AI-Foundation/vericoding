use vstd::prelude::*;

verus! {

// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn longest_prefix(a: &[i32], b: &[i32]) -> (i: usize)
    ensures 
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i as int] != b[i as int]
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len() && a[i] == b[i]
        invariant
            i <= a.len(),
            i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
        decreases
            a.len() - i
    {
        proof {
            assert(a@.subrange(0, i as int) == b@.subrange(0, i as int));
            assert(a@[i as int] == b@[i as int]);
            assert(a@.subrange(0, (i + 1) as int) =~= a@.subrange(0, i as int).push(a@[i as int]));
            assert(b@.subrange(0, (i + 1) as int) =~= b@.subrange(0, i as int).push(b@[i as int]));
        }
        
        i = i + 1;
    }
    
    // After the loop exits, we know:
    // - i <= a.len() && i <= b.len() (from invariants)
    // - a@.subrange(0, i as int) == b@.subrange(0, i as int) (from invariants)
    // - If i < a.len() && i < b.len(), then a[i] != b[i] (because loop exited due to inequality)
    
    i
}
// </vc-code>

fn main() {
    // Test method with an example.
}

}