use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut max_len: usize = lists[0].len();
    
    for i in 1..lists.len()
        invariant
            0 <= max_idx < lists.len(),
            1 <= i <= lists.len(),
            max_len == lists[max_idx as int].len(),
            forall|j: int| 0 <= j < i ==> #[trigger] lists[j].len() <= max_len,
            max_idx < i,
    {
        if lists[i].len() > max_len {
            max_idx = i;
            max_len = lists[i].len();
        }
    }
    
    assert(max_idx < lists.len());
    assert(forall|j: int| 0 <= j < lists.len() ==> lists[j].len() <= max_len);
    assert(max_len == lists[max_idx as int].len());
    
    let result = lists[max_idx].clone();
    assert(result@ == lists[max_idx as int]@);
    assert(exists|i: int| 0 <= i < lists.len() && result@ == lists[i]@) by {
        assert(result@ == lists[max_idx as int]@);
    };
    
    result
}
// </vc-code>

fn main() {}

}