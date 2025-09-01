use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn min(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}

proof fn min_exists_in_vec(lists: Seq<Seq<i32>>, i: int, j: int)
    requires
        0 <= i < lists.len(),
        0 <= j < lists.len(),
    ensures
        min(lists[i].len() as usize, lists[j].len() as usize) <= lists[i].len() as usize,
        min(lists[i].len() as usize, lists[j].len() as usize) <= lists[j].len() as usize,
        exists|k: int| 0 <= k < lists.len() && min(lists[i].len() as usize, lists[j].len() as usize) == lists[k].len() as usize
{
    if lists[i].len() as usize <= lists[j].len() as usize {
        assert(min(lists[i].len() as usize, lists[j].len() as usize) == lists[i].len() as usize);
        assert(0 <= i < lists.len());
    } else {
        assert(min(lists[i].len() as usize, lists[j].len() as usize) == lists[j].len() as usize);
        assert(0 <= j < lists.len());
    }
}

proof fn min_transitive(lists: Seq<Seq<i32>>, current_min: usize, i: int)
    requires
        0 <= i < lists.len(),
        current_min <= lists[i].len() as usize,
        exists|k: int| 0 <= k < lists.len() && current_min == lists[k].len() as usize
    ensures
        exists|k: int| 0 <= k < lists.len() && min(current_min, lists[i].len() as usize) == lists[k].len() as usize,
        min(current_min, lists[i].len() as usize) <= lists[i].len() as usize,
{
    if current_min <= lists[i].len() as usize {
        assert(min(current_min, lists[i].len() as usize) == current_min);
    } else {
        assert(min(current_min, lists[i].len() as usize) == lists[i].len() as usize);
        assert(0 <= i < lists.len());
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    // pre-conditions-start
    requires
        lists.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut min_len: usize = lists[0].len();
    proof {
        assert(0 <= 0 < lists.len());
        assert(exists|i: int| 0 <= i < lists.len() && min_len == lists[i].len());
    }
    
    let mut index: usize = 1;
    while index < lists.len()
        invariant
            index <= lists.len(),
            exists|i: int| 0 <= i < lists.len() && min_len == lists[i].len(),
            forall|j: int| 0 <= j < index ==> min_len <= lists[j].len(),
    {
        let current_len: usize = lists[index].len();
        if current_len < min_len {
            min_len = current_len;
            proof {
                assert(0 <= index < lists.len());
                assert(min_len == lists[index].len());
            }
        } else {
            proof {
                assert(min_len <= current_len);
            }
        }
        
        proof {
            assert forall|j: int| 0 <= j < index + 1 implies min_len <= lists[j].len() by {
                if j < index {
                    assert(0 <= j < index);
                    assert(min_len <= lists[j].len());
                } else {
                    assert(j == index);
                    assert(min_len <= lists[j].len());
                }
            }
        }
        
        index += 1;
    }
    
    min_len
}
// </vc-code>

fn main() {}
}