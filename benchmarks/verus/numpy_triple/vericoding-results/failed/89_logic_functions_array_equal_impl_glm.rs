// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof blocks to show ghost indexing and maintain loop invariant */
fn find_first_mismatch_index<T>(a1: &Vec<T>, a2: &Vec<T>) -> (idx: Option<usize>)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures
        match idx {
            Some(i) => 0 <= i < a1.len() as int && a1@[i as int] != a2@[i as int] &&
                      forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j],
            None => forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i],
        },
{
    let mut i = 0;
    while i < a1.len()
        invariant
            0 <= i <= a1.len() as int,
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j],
        decreases a1.len() as int - i
    {
        assert(i < a2.len()); // because a1.len() == a2.len() and i < a1.len()
        if a1[i] != a2[i] {
            proof {
                // Show that the ghost indexing has a mismatch at i
                assert(a1@[i as int] != a2@[i as int]);
            }
            return Some(i);
        }
        i += 1;
        proof {
            // After incrementing, we have i = old_i + 1.
            // We need to show: forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j]
            // We know from the invariant at the start of the iteration that for j in [0, old_i) they are equal.
            // And we checked that a1[old_i] == a2[old_i] so a1@[old_i] == a2@[old_i].
            // Therefore, for any j in [0, i) (which is [0, old_i+1)), we have a1@[j] == a2@[j].
            // We can break the range into [0, old_i) and [old_i, old_i+1) (i.e., j=old_i).
            // But note: the invariant already covers [0, old_i), and we have the element at old_i.
            // So we can combine.
            assert(forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j]);
        }
    }
    None
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() as int && !(a1@[i] == a2@[i]) ==> result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): improved proof blocks to explicitly show postcondition conditions */
{
    let idx = find_first_mismatch_index(a1, a2);
    match idx {
        Some(i) => {
            proof {
                // We have from the helper's postcondition:
                //   - 0 <= i < a1.len() as int
                //   - a1@[i] != a2@[i]
                //   - forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j]
                // Therefore, the arrays are not universally equal because of the mismatch at i.
                assert( !(forall|k: int| 0 <= k < a1.len() as int ==> a1@[k] == a2@[k]) );
                // Also, there exists an index (namely i) with a mismatch.
                assert( exists|k: int| 0 <= k < a1.len() as int && a1@[k] != a2@[k] );
            }
            false
        },
        None => {
            proof {
                // From the helper's postcondition: for all indices, the arrays are equal.
                assert( forall|k: int| 0 <= k < a1.len() as int ==> a1@[k] == a2@[k] );
                // Therefore, there does not exist an index with a mismatch.
                assert( !(exists|k: int| 0 <= k < a1.len() as int && a1@[k] != a2@[k]) );
            }
            true
        },
    }
}
// </vc-code>

}
fn main() {}