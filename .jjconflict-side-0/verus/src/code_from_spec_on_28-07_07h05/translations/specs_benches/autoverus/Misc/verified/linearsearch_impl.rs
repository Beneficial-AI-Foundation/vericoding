#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
//IMPL linear_search
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums@.len() < 0x8000_0000,
ensures
    ret < nums@.len(),
    ret >=0 ==> nums@[ret as int] == target,
    ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i]!= target,
    ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target,
{
    let mut i = 0;
    while i < nums.len()
    invariant
        0 <= i <= nums@.len(),
        forall |j: int| 0 <= j < i ==> #[trigger]nums@[j] != target,
        /* code modified by LLM (iteration 3): strengthened invariant to ensure i stays bounded after increment */
        i <= nums@.len() && nums@.len() < 0x8000_0000,
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    decreases nums@.len() - i
    {
        if nums[i] == target {
            /* code modified by LLM (iteration 1): added assertion to help verify postcondition and cast bounds */
            assert(nums@[i as int] == target);
            assert(i < nums@.len());
            /* code modified by LLM (iteration 3): added assertion to ensure cast safety before return */
            assert(i < 0x8000_0000);
            return i as i32;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): added assertion to help verify the postcondition when target not found */
    assert(forall |j: int| 0 <= j < nums@.len() ==> nums@[j] != target);
    return -1;
}
}