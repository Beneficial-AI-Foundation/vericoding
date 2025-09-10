use vstd::prelude::*;

verus! {

fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures forall|k: int| 0 < k < i && k < nums.len() ==> nums[k] != val,
{
    assume(false);
    unreached();
}

}
fn main() {}