use vstd::prelude::*;


verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    // pre-conditions-start
    requires
        list.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut min = list[0].len();
    let mut min_index = 0;
    
    let mut i = 1;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            min == list[min_index as int].len(),
            0 <= min_index < i,
            forall|j: int| 0 <= j < i ==> min <= #[trigger] list[j].len(),
            exists|j: int| 0 <= j < i && min == #[trigger] list[j].len(),
        decreases list.len() - i,
    {
        if list[i].len() < min {
            min = list[i].len();
            min_index = i;
        }
        i += 1;
    }
    
    min
}
// </vc-code>

} // verus!

fn main() {}