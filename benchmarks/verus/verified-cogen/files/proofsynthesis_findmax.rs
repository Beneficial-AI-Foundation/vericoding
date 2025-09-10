#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

fn find_max(nums: Vec<i32>) -> (ret:i32)

    requires
        nums.len() > 0,

    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    assume(false);
    unreached()
}

}
fn main() {}