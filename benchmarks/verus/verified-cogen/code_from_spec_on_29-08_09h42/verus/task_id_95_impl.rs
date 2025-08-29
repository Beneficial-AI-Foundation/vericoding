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
    let mut index = 1;
    
    /* code modified by LLM (iteration 2): added decreases clause */
    while index < list.len()
        invariant
            0 < index <= list.len(),
            min >= 0,
            forall|i: int| 0 <= i < index ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < index && min == #[trigger] list[i].len(),
        decreases list.len() - index,
    {
        if list[index].len() < min {
            min = list[index].len();
        }
        index += 1;
    }
    
    min
}
// </vc-code>

} // verus!

fn main() {}