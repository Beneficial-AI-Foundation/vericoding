use vstd::prelude::*;

verus! {

fn count_arrays(arrays: &Vec<Vec<i32>>) -> (count: usize)
    ensures 
        count >= 0,
        count == arrays.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}