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
    let split_point = rotation_split(list.len(), n) as usize;
    let mut new_list = Vec::new();
    
    // Add elements from split_point to end
    let mut i = split_point;
    while i < list.len()
        invariant
            new_list.len() == i - split_point,
            i >= split_point,
            i <= list.len(),
            new_list@ == list@.subrange(split_point as int, i as int),
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Add elements from beginning to split_point
    let mut j = 0;
    while j < split_point
        invariant
            j <= split_point,
            new_list.len() == (list.len() - split_point) + j,
            new_list@ == list@.subrange(split_point as int, list@.len() as int).add(
                list@.subrange(0, j as int)
            ),
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!