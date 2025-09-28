// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)

    requires
        list.len() > 0,
        0 < k < list@.len(),

    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed arithmetic overflow and invariant issues */
    let mut new_list = Vec::new();
    let mut i: usize = 0;
    while i < list.len()
        invariant
            i <= list.len(),
            new_list@.len() == if i < k { i as int } else { (i - 1) as int },
            forall|j: int| 0 <= j < new_list@.len() ==> {
                if i <= k {
                    new_list@[j] == list@[j]
                } else {
                    if j < k - 1 {
                        new_list@[j] == list@[j]
                    } else {
                        new_list@[j] == list@[j + 1]
                    }
                }
            },
        decreases list.len() - i
    {
        if i + 1 != k {
            new_list.push(list[i]);
        }
        i = i + 1;
    }
    new_list
}
// </vc-code>

}
fn main() {}