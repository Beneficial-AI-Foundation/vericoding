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
    let mut max_index: usize = 0;
    let mut max_len_usize: usize = lists[0].len();
    let n = lists.len();

    let ghost mut max_len_ghost: int;
    proof {
        max_len_ghost = lists[0].len() as int;
    }

    for i in 1..n
        invariant
            0 <= max_index < i,
            max_len_ghost == (lists[max_index].len() as int),
            forall|j: int| 0 <= j < (i as int) ==> (lists@[j].len() as int) <= max_len_ghost,
            exists|j: int| 0 <= j < (i as int) && (max_len_ghost == lists@[j].len() as int)
    {
        let current_len_usize = lists[i].len();
        if current_len_usize > max_len_usize {
            max_index = i;
            max_len_usize = current_len_usize;
            proof {
                max_len_ghost = current_len_usize as int;
            }
        }
    }

    lists[max_index].clone()
}
// </vc-code>

fn main() {}

}