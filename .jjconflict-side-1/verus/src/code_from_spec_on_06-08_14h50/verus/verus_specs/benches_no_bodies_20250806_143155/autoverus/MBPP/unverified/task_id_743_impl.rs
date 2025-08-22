use vstd::prelude::*;
fn main() {}

verus! {

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    requires
        list.len() > 0,
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
{
    let len = list.len();
    let split_point = len - (n % len);
    
    let mut new_list = Vec::new();
    
    // Add elements from split_point to end
    let mut i = split_point;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < len
        invariant
            new_list.len() == i - split_point,
            new_list@ == list@.subrange(split_point as int, i as int),
        decreases len - i,
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Add elements from beginning to split_point
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while j < split_point
        invariant
            new_list.len() == (len - split_point) + j,
            new_list@ == list@.subrange(split_point as int, len as int).add(
                list@.subrange(0, j as int)
            ),
        decreases split_point - j,
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!