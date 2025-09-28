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
    let mut i: i32 = 0;

    while i < a.len() as i32
        invariant 0 <= i as int && i as int <= a.len() as int
        invariant forall|k: int| 0 <= k && k < i as int ==> a[k] != key
        decreases a.len() as int - i as int
    {
        assert(0 <= i as int);
        assert(i as int < a.len() as int);

        if a[i as int] == key {
            return i;
        } else {
            let old_i = i;
            assert(a[old_i as int] != key);
            i = i + 1;
            assert(i as int == old_i as int + 1);

            proof {
                assert forall|k: int|
                    0 <= k && k < i as int ==> a[k] != key by
                {
                    if k < old_i as int {
                        assert(a[k] != key);
                    } else {
                        assert(k >= old_i as int);
                        assert(k < old_i as int + 1);
                        assert(k == old_i as int);
                        assert(a[old_i as int] != key);
                        assert(a[k] != key);
                    }
                }
            }
        }
    }

    assert(!(i < a.len() as i32));
    assert(i >= a.len() as i32);
    assert(i as int >= a.len() as int);
    assert(i as int <= a.len() as int);
    assert(i as int == a.len() as int);

    proof {
        assert forall|k: int|
            0 <= k && k < a.len() as int ==> a[k] != key by
        {
            assert(k < i as int);
            assert(a[k] != key);
        }
    }

    -1
}
// </vc-code>

fn main() {
}

}