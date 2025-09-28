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
    let mut i: nat = 0;
    let mut found_idx: int = -1;

    while i < a.len()
        invariant
            i <= a.len(),
            // If found_idx is non-negative, then it's the index where `key` was found AND `key` doesn't appear before `found_idx`
            found_idx >= 0 ==> (
                found_idx < i as int &&
                a[found_idx as int] == key &&
                (forall|k: int| 0 <= k < found_idx ==> a[k as int] != key)
            ),
            // If found_idx is negative, then `key` has not been found in `a[0..i-1]`
            found_idx < 0 ==> (
                (forall|k: int| 0 <= k < i as int ==> a[k as int] != key)
            ),
        decreases a.len() - i
    {
        if found_idx < 0 && a[i as int] == key {
            found_idx = i as int;
        }
        i = i + 1;
    }

    found_idx
}
// </vc-code>

fn main() {
}

}