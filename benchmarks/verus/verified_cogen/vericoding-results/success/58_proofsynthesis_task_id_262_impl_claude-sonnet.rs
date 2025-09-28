// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))

    requires
        list@.len() > 0,
        0 < l < list@.len(),

    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): add decreases clause to while loop */
    let mut first_part = Vec::new();
    let mut second_part = Vec::new();
    
    let mut i = 0;
    while i < list.len()
        invariant
            i <= list.len(),
            first_part.len() == if i <= l { i } else { l },
            second_part.len() == if i <= l { 0 } else { i - l },
            forall|j: int| 0 <= j < first_part.len() ==> first_part@[j] == list@[j],
            forall|j: int| 0 <= j < second_part.len() ==> second_part@[j] == list@[l + j],
        decreases list.len() - i
    {
        if i < l {
            first_part.push(list[i]);
        } else {
            second_part.push(list[i]);
        }
        i += 1;
    }
    
    (first_part, second_part)
}
// </vc-code>

}
fn main() {}