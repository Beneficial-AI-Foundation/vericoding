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
    let tracked a_seq = vstd::slice::slice_to_seq(a);
    let a_len = a.len();
    let mut index: i32 = -1;
    let mut i: usize = 0;
    while i < a_len
        invariant(0 <= i <= a_len as int)
        invariant(forall|k: int| #[trigger] (0 <= k < i as int ==> a_seq@[k] != key))
    {
        if a[i] == key
        {
            proof {
                assert(a_seq@[i as int] == key && forall|k: int| 0 <= k < i as int ==> a_seq@[k] != key);
            };
            index = i as i32;
            return index;
        }
        else
        {
            proof {
                assert(a_seq@[i as int] != key);
            };
            i += 1;
        }
    }
    proof {
        assert(forall|k: int| 0 <= k < a_len as int ==> a_seq@[k] != key);
    };
    index
}
// </vc-code>

fn main() {
}

}