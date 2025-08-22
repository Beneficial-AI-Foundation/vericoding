use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    // pre-conditions-start
    requires
        list.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
    // post-conditions-end
{
    let mut new_list = Vec::new();
    let len = list.len();
    let split_point = len - (n % len);
    
    // Add elements from split_point to end
    let mut i = split_point;
    /* code modified by LLM (iteration 1): added decreases clause for termination proof */
    while i < len
        invariant
            new_list.len() == i - split_point,
            new_list@ == list@.subrange(split_point as int, i as int),
        decreases len - i
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Add elements from start to split_point
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination proof */
    while j < split_point
        invariant
            new_list.len() == (len - split_point) + j,
            new_list@ == list@.subrange(split_point as int, len as int).add(
                list@.subrange(0, j as int)
            ),
        decreases split_point - j
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!

fn main() {}