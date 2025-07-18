use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

/* code modified by LLM (iteration 3): Fixed function signature syntax and implementation */
fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
{
    return false;  // TODO: Remove this line and implement the function body
}
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
    /* code modified by LLM (iteration 3): Implemented function body to perform right rotation */
    let len = list.len();
    let split_point = len - (n % len);
    
    let mut new_list = Vec::new();
    
    // Add elements from split_point to end
    let mut i = split_point;
    while i < len
        invariant
            i <= len,
            new_list.len() == i - split_point,
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
            new_list.len() == (len - split_point) + j,
            new_list@ == list@.subrange(split_point as int, len as int).add(
                list@.subrange(0, j as int)
            ),
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!

fn main() {}