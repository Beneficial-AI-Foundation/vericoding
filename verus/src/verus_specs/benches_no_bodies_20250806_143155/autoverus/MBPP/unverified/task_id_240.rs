use vstd::prelude::*;

fn main() {}

verus! {

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
