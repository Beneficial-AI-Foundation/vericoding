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
// (no helpers needed)
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
    let mut i: i32 = 0;
    while (i as int) < a.len() && a[i as int] != key
        invariant 0 <= (i as int) && (i as int) <= a.len() &&
                  forall |k: int| 0 <= k < (i as int) ==> a[k] != key;
        decreases a.len() - ((i as int) as nat);
    {
        i = i + 1;
    }

    if (i as int) < a.len() {
        proof {
            // From loop exit and the fact (i < a.len()) we get a[i] == key
            assert(!((i as int) < a.len() && a[i as int] != key));
            assert((i as int) < a.len());
            assert(a[i as int] == key);
            // The invariant already gives forall k < i ==> a[k] != key
            assert(forall |k: int| 0 <= k < (i as int) ==> a[k] != key);
        }
        i
    } else {
        proof {
            // From loop invariant and bounds we get i == a.len()
            assert(!((i as int) < a.len() && a[i as int] != key));
            assert(!((i as int) < a.len()));
            assert((i as int) >= a.len());
            assert((i as int) <= a.len());
            assert((i as int) == a.len());
            // Thus forall k < a.len() ==> a[k] != key
            assert(forall |k: int| 0 <= k < a.len() ==> a[k] != key);
        }
        -1
    }
}
// </vc-code>

fn main() {
}

}