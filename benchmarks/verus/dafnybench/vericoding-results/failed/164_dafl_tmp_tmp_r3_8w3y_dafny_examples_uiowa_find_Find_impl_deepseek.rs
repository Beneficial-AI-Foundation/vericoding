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
proof fn lemma_seq_index_find(s: Seq<i32>, key: i32, i: int)
    requires
        0 <= i < s.len(),
        s[i] == key,
        forall|k: int| 0 <= k < i ==> s[k] != key
    ensures
        forall|k: int| 0 <= k < i ==> s[k] != key
{
}

proof fn lemma_seq_no_key(s: Seq<i32>, key: i32, len: int)
    requires
        len >= 0,
        forall|k: int| 0 <= k < len ==> s[k] != key
    ensures
        forall|k: int| 0 <= k < len ==> s[k] != key
{
}

proof fn lemma_len_cast(a: &[i32])
    ensures
        a.len() as i32 >= 0,
        forall|i: int| 0 <= i < a.len() ==> 0 <= i as i32 <= a.len() as i32
{
    assert forall|i: int| 0 <= i < a.len() implies 0 <= i as i32 <= a.len() as i32 by {
        assert(0 <= i < a.len());
        assert(0 <= i as i32);
        assert(i as i32 <= a.len() as i32);
    };
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
    let mut idx: i32 = 0;
    let ghost mut s = Seq::<i32>::empty();
    proof {
        s = a@;
        lemma_len_cast(a);
    }
    while idx < a.len() as i32
        invariant
            0 <= idx <= a.len() as i32,
            forall|k: int| 0 <= k < idx as int ==> a[k] != key,
        decreases (a.len() as i32) - idx
    {
        if a[idx as usize] == key {
            proof {
                lemma_seq_index_find(s, key, idx as int);
            }
            return idx;
        }
        proof {
            assert(a[idx as int] != key);
            assert forall|k: int| 0 <= k < idx as int + 1 implies a[k] != key by {
                if k < idx as int {
                    // Already in invariant
                } else if k == idx as int {
                    assert(a[idx as int] != key);
                }
            };
        }
        idx = idx + 1;
    }
    proof {
        lemma_seq_no_key(s, key, a.len() as int);
    }
    -1
}
// </vc-code>

fn main() {
}

}