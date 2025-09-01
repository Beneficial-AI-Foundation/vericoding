use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    let mut min_len = lists[0].len();
    let mut i: usize = 1;
    
    assert(exists|j: int| 0 <= j < 1 && min_len == lists[j as usize].len()) by {
        assert(min_len == lists[0].len());
    }
    
    while i < lists.len()
        invariant
            1 <= i <= lists.len(),
            lists.len() > 0,
            exists|j: int| #![auto] 0 <= j < i && min_len == lists[j as usize].len(),
            forall|j: int| #![auto] 0 <= j < i ==> min_len <= lists[j as usize].len(),
    {
        if lists[i].len() < min_len {
            min_len = lists[i].len();
            assert(exists|j: int| 0 <= j < i + 1 && min_len == lists[j as usize].len()) by {
                assert(min_len == lists[i].len());
                assert(0 <= i < i + 1);
            }
            assert(forall|j: int| 0 <= j < i + 1 ==> min_len <= lists[j as usize].len()) by {
                assert(min_len == lists[i].len());
                assert(forall|j: int| 0 <= j < i ==> lists[i].len() < lists[j as usize].len() || lists[i].len() == lists[j as usize].len());
            }
        } else {
            assert(exists|j: int| 0 <= j < i + 1 && min_len == lists[j as usize].len()) by {
                assert(exists|j: int| 0 <= j < i && min_len == lists[j as usize].len());
            }
            assert(forall|j: int| 0 <= j < i + 1 ==> min_len <= lists[j as usize].len()) by {
                assert(min_len <= lists[i].len());
                assert(forall|j: int| 0 <= j < i ==> min_len <= lists[j as usize].len());
            }
        }
        i = i + 1;
    }
    
    assert(i == lists.len());
    assert(exists|j: int| 0 <= j < lists.len() && min_len == lists[j as usize].len());
    assert(forall|j: int| 0 <= j < lists.len() ==> min_len <= lists[j as usize].len());
    
    min_len
}
// </vc-code>

fn main() {}
}