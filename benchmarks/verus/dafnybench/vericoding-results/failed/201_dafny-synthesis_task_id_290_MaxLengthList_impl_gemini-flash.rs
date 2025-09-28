use vstd::prelude::*;

verus! {

// <vc-helpers>
fn get_max_len_list_idx(lists: &Vec<Vec<int>>) -> (max_idx: usize)
    requires lists.len() > 0
    ensures 0 <= max_idx < lists.len()
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= lists[max_idx].len()
{
    let mut max_len: int = -1;
    let mut max_idx: usize = 0;
    let mut i: usize = 0;

    // Prove the initial invariant for the loop
    proof {
        if lists.len() > 0 {
            // max_idx is initialized to 0, which is a valid index
            assert(0 <= max_idx);
            assert(max_idx < lists.len());

            // The 'i' is initialized to 0. So, the range 0 <= k < i is empty.
            // The forall statement (forall|k: int| 0 <= k < i ==> lists[k].len() <= lists[max_idx].len())
            // is vacuously true initially.
            assert(lists[max_idx].len() as int == max_len);
        }
    }

    while i < lists.len()
        invariant 0 <= i <= lists.len()
        invariant 0 <= max_idx < lists.len()
        invariant lists.len() > 0 ==> lists[max_idx].len() as int == max_len
        invariant forall|k: int| 0 <= k < i ==> #[trigger] lists[k].len() <= #[trigger] lists[max_idx].len()
    {
        if (lists[i].len() as int) > max_len {
            max_len = lists[i].len() as int;
            max_idx = i;
        }

        proof {
            // Prove that the invariant holds for the next iteration
            // We need to show that forall|k: int| 0 <= k < (i+1) ==> lists[k].len() <= lists[max_idx_next].len()
            // where max_idx_next is the value of max_idx in the next iteration.

            if (lists[i].len() as int) <= max_len {
                // max_idx is not updated
                assert(lists[i].len() as int <= lists[max_idx].len() as int);
                assert forall|k: int| 0 <= k < (i+1) implies lists[k].len() <= lists[max_idx].len() by {
                    if (k as usize) < i {
                        assert(lists[k].len() <= lists[max_idx as usize].len());
                    } else if (k as usize) == i {
                        assert(lists[i].len() <= lists[max_idx as usize].len());
                    }
                }
            } else {
                // max_idx is updated to i
                assert forall|k: int| 0 <= k < (i+1) implies lists[k].len() <= lists[i].len() by {
                    if (k as usize) < i {
                        assert(lists[k].len() <= lists[max_idx].len()); // old max_idx
                        assert(lists[k].len() as int <= max_len); // from older invariant
                        assert(max_len < lists[i].len() as int);
                        assert(lists[k].len() as int < lists[i].len() as int);
                    } else if (k as usize) == i {
                        assert(lists[i].len() == lists[i].len());
                    }
                }
            }
            if lists.len() > 0 {
                assert(lists[max_idx].len() as int == max_len);
            }
        }
        i = i + 1;
    }
    max_idx
}
// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let max_idx = get_max_len_list_idx(lists);
    let max_list = lists[max_idx].clone();

    proof {
        // Prove the first ensures clause: forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len()
        assert forall|i: int| 0 <= i < lists.len() implies lists[i].len() <= max_list.len() by {
            // This directly follows from the postcondition of get_max_len_list_idx
            // which states: forall|k: int| 0 <= k < lists.len() ==> lists[k].len() <= lists[max_idx].len()
            // Since max_list.len() is equal to lists[max_idx].len(), the property holds.
            assert(lists[i].len() <= lists[max_idx].len()); // this comes from postcondition of get_max_len_list_idx
            assert(max_list.len() == lists[max_idx].len());
        }

        // Prove the second ensures clause: exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
        assert exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@ by {
            // We can pick the max_idx found by the helper function.
            let i = max_idx as int;
            assert(0 <= i);
            assert((i as usize) < lists.len()); // From postcondition of get_max_len_list_idx: 0 <= max_idx < lists.len()
            assert(max_list@ == lists[max_idx]@); // By definition of max_list
        }
    }
    max_list
}
// </vc-code>

fn main() {}

}