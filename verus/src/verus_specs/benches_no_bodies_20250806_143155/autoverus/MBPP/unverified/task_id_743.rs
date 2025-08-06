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
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
