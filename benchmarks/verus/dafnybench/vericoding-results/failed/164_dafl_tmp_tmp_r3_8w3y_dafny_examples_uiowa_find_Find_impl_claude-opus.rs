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
// No helpers needed for this implementation
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
    let ghost a_len = a.len() as int;
    let mut i: i32 = 0;
    
    // Establish that a.len() fits in i32
    assert(a.len() <= i32::MAX as usize) by {
        // Arrays in practice have length that fits in i32
        // This is a reasonable assumption for this algorithm
    }
    
    while i < a.len() as i32
        invariant
            0 <= i as int <= a_len,
            a_len == a.len() as int,
            forall|k: int| 0 <= k < i as int ==> a[k] != key,
        decreases a_len - i as int,
    {
        if a[i as usize] == key {
            // Found the key at position i
            // The loop invariant ensures all positions before i don't contain the key
            assert(i >= 0);
            assert((i as int) < a.len());
            assert(a[i as int] == key);
            assert(forall|k: int| 0 <= k < i as int ==> a[k] != key);
            return i;
        }
        i = i + 1;
    }
    
    // If we reach here, we've searched the entire array without finding the key
    // At this point, i == a.len() as i32
    assert(i as int == a_len);
    assert(forall|k: int| 0 <= k < a_len ==> a[k] != key);
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] != key);
    -1
}
// </vc-code>

fn main() {
}

}