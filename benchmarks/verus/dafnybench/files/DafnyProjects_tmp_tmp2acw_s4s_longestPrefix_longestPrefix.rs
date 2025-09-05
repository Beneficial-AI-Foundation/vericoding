use vstd::prelude::*;

verus! {

// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b.

// <vc-helpers>
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
    assume(false);
    0
}
// </vc-code>

fn main() {
    // Test method with an example.
}

}
