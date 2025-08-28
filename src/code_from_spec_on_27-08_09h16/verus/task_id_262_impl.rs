use vstd::prelude::*;


verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    // pre-conditions-start
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut first_part = Vec::new();
    let mut second_part = Vec::new();
    
    let mut i = 0;
    while i < l
        invariant
            i <= l,
            l < list.len(),
            first_part@.len() == i,
            forall|j: int| 0 <= j < i ==> first_part@[j] == list@[j],
        decreases l - i,
    {
        first_part.push(list[i]);
        i += 1;
    }
    
    let mut j = l;
    while j < list.len()
        invariant
            l <= j <= list.len(),
            second_part@.len() == j - l,
            forall|k: int| 0 <= k < j - l ==> second_part@[k] == list@[l + k],
        decreases list.len() - j,
    {
        second_part.push(list[j]);
        j += 1;
    }
    
    (first_part, second_part)
}
// </vc-code>

} // verus!

fn main() {}