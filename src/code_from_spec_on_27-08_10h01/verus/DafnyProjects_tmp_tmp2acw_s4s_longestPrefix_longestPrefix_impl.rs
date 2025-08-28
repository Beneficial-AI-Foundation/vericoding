use vstd::prelude::*;

verus! {

// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn longest_prefix(a: &[i32], b: &[i32]) -> (i: usize)
    ensures 
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i as int] != b[i as int]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    while i < a.len() && i < b.len() && a[i] == b[i]
        invariant
            i <= a.len() && i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
        decreases a.len() - i
    {
        i += 1;
        proof {
            assert(a@.subrange(0, (i-1) as int) == b@.subrange(0, (i-1) as int));
            assert(a[i-1] == b[i-1]);
            assert(a@.subrange(0, i as int) =~= a@.subrange(0, (i-1) as int).push(a[i-1]));
            assert(b@.subrange(0, i as int) =~= b@.subrange(0, (i-1) as int).push(b[i-1]));
        }
    }
    i
}
// </vc-code>

fn main() {
    // Test method with an example.
}

}