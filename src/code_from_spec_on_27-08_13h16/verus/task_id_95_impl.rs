use vstd::prelude::*;


verus! {

// <vc-helpers>
// No updates needed for helpers
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
    let mut min_length: usize = list[0].len();
    let mut i: usize = 1;

    while i < list.len()
        invariant
            i <= list.len(),
            forall|k: int| 0 <= k < i ==> min_length <= list[k].len(),
            exists|k: int| 0 <= k < i && min_length == list[k].len(),
        decreases list.len() - i
    {
        if list[i].len() < min_length {
            min_length = list[i].len();
        }
        i = i + 1;
    }

    min_length
}
// </vc-code>

} // verus!

fn main() {}