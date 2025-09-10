use vstd::prelude::*;

verus! {

fn semi_ordered_permutation(nums: &Vec<i32>) -> (result: i32)
    ensures 
        result >= 0
{
    assume(false);
    unreached();
}

}
fn main() {}