use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let mut max_list = &lists[0];
    let mut max_len = lists[0].len();
    let mut max_index: usize = 0;
    
    for i in 1..lists.len()
        invariant
            0 < lists.len(),
            max_len == max_list.len(),
            max_index < lists.len(),
            max_list@ == lists[max_index as int]@,
            forall|j: int| 0 <= j < i ==> #[trigger] lists[j].len() <= max_len,
            lists[max_index as int].len() == max_len,
            max_index as int < i,
    {
        if lists[i].len() > max_len {
            max_list = &lists[i];
            max_len = lists[i].len();
            max_index = i;
        }
    }
    
    assert(max_index < lists.len());
    assert(max_list@ == lists[max_index as int]@);
    assert(forall|j: int| 0 <= j < lists.len() ==> #[trigger] lists[j].len() <= max_len);
    
    max_list.clone()
}
// </vc-code>

fn main() {}

}