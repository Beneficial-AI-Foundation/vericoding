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
    let len = list.len();
    let split = len - (n % len);
    let mut result = Vec::new();
    
    // Add elements from split position to end
    let mut i = split;
    while i < len
        invariant
            i <= len,
            split <= len,
            result.len() == i - split,
            result@ == list@.subrange(split as int, i as int),
    {
        result.push(list[i]);
        i += 1;
    }
    
    // Add elements from beginning to split position
    i = 0;
    while i < split
        invariant
            i <= split,
            split <= len,
            result.len() == (len - split) + i,
            result@ == list@.subrange(split as int, len as int).add(list@.subrange(0, i as int)),
    {
        result.push(list[i]);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}