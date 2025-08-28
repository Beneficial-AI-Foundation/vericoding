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
proof fn lemma_min_index(a: Seq<i32>, key: i32, i: int)
    requires
        0 <= i < a.len(),
        a[i] == key,
        forall|k: int| 0 <= k < i ==> a[k] != key,
    ensures
        forall|k: int| 0 <= k < i ==> a[k] != key,
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn find(a: &[i32], key: i32) -> (i: i32)
    ensures
        0 <= i ==> (
            i < a.len() as i32 && 
            a[i as usize] == key && 
            forall|k: int| 0 <= k < i ==> a[k] != key
        ),
        i < 0 ==> 
            forall|k: int| 0 <= k < a.len() as i32 ==> a[k] != key,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i as i32 ==> a[k] != key,
    {
        if a[i] == key {
            return i as i32;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

fn main() {
}

}