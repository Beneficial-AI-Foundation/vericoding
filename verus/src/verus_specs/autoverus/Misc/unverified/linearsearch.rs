#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums@.len() < 0x8000_0000,
ensures
    ret < nums@.len(),
    ret >=0 ==> nums@[ret as int] == target,
    ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i]!= target,
    ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target,
{
    return 0;  // TODO: Remove this line and implement the function body
}
}
