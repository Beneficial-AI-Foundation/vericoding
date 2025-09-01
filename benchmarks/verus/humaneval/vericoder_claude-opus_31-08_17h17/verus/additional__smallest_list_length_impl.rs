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
    
    assert(exists|j: int| 0 <= j < 1 && min_len == lists@[j].len()) by {
        assert(min_len == lists[0].len());
        assert(lists@[0].len() == lists[0].len());
    }
    
    while i < lists.len()
        invariant
            1 <= i <= lists.len(),
            lists.len() > 0,
            exists|j: int| #![auto] 0 <= j < i && min_len == lists@[j].len(),
            forall|j: int| #![auto] 0 <= j < i ==> min_len <= lists@[j].len(),
    {
        if lists[i].len() < min_len {
            min_len = lists[i].len();
            assert(exists|j: int| 0 <= j < i + 1 && min_len == lists@[j].len()) by {
                assert(min_len == lists[i].len());
                assert(lists@[i as int].len() == lists[i].len());
                assert(0 <= i as int && i as int < i as int + 1);
            }
            assert(forall|j: int| 0 <= j < i + 1 ==> min_len <= lists@[j].len()) by {
                assert(min_len == lists[i].len());
                assert(lists@[i as int].len() == lists[i].len());
                assert(forall|j: int| 0 <= j < i ==> lists@[i as int].len() < lists@[j].len() || lists@[i as int].len() == lists@[j].len());
            }
        } else {
            assert(exists|j: int| 0 <= j < i + 1 && min_len == lists@[j].len()) by {
                assert(exists|j: int| 0 <= j < i && min_len == lists@[j].len());
            }
            assert(forall|j: int| 0 <= j < i + 1 ==> min_len <= lists@[j].len()) by {
                assert(min_len <= lists[i].len());
                assert(lists@[i as int].len() == lists[i].len());
                assert(forall|j: int| 0 <= j < i ==> min_len <= lists@[j].len());
            }
        }
        i = i + 1;
    }
    
    assert(i == lists.len());
    assert(exists|j: int| 0 <= j < lists.len() && min_len == lists@[j].len());
    assert(forall|j: int| 0 <= j < lists.len() ==> min_len <= lists@[j].len());
    
    min_len
}
// </vc-code>

fn main() {}
}