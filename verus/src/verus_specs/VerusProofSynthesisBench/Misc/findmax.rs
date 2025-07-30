#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
fn find_max(nums: Vec<i32>) -> (ret:i32)
    // pre-conditions-start
    requires
        nums.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}
}


fn main() {}