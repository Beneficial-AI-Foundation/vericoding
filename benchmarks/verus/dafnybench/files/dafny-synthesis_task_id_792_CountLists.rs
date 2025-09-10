use vstd::prelude::*;

verus! {

fn count_lists(lists: &Vec<Vec<int>>) -> (count: usize)
    ensures 
        count >= 0,
        count == lists.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}