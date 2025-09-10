use vstd::prelude::*;

verus! {

fn rain(heights: &Vec<i32>) -> (result: i32)
    requires forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 0,
    ensures 
        result >= 0,
        heights.len() < 3 ==> result == 0,
{
    assume(false);
    unreached()
}

}
fn main() {}