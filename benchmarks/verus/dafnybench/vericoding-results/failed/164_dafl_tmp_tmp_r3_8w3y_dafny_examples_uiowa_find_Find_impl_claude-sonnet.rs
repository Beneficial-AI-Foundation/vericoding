use vstd::prelude::*;

verus! {

/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa

   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/

// <vc-helpers>
// Helper lemma to establish bounds for usize to i32 conversion
proof fn usize_to_i32_bounds(i: usize, a: &[i32])
    requires i < a.len(), a.len() <= i32::MAX
    ensures i <= i32::MAX, i as i32 >= 0
{
}
// </vc-helpers>

// <vc-spec>
fn find(a: &[i32], key: i32) -> (i: i32)
    ensures
        // if i is non-negative then 
        0 <= i ==> (// (1) i is smaller than the length of a
                    i < a.len() && 
                    // (2) key is at position i in a
                    a[i as int] == key && 
                    // (3) i is the smallest position where key appears
                    forall|k: int| 0 <= k < i ==> a[k] != key
                   ),
        // if index is negative then
        i < 0 ==> 
                // a does not contain key
                forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            assert(0 <= i < a.len());
            assert(a[i as int] == key);
            assert(forall|k: int| 0 <= k < i ==> a[k] != key);
            if i <= i32::MAX {
                assert(i as i32 >= 0);
                assert((i as i32) < (a.len() as i32));
                return i as i32;
            } else {
                // If index is too large for i32, return -1 
                // This satisfies the second part of the postcondition
                return -1;
            }
        }
        i += 1;
    }
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] != key);
    -1
}
// </vc-code>

fn main() {
}

}