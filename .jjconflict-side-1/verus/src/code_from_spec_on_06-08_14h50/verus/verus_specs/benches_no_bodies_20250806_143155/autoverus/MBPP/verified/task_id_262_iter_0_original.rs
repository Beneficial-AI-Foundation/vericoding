use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!
