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
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums@.len(),
            forall |j: int| 0 <= j < i as int ==> #[trigger]nums@[j] != target,
            /* code modified by LLM (iteration 2): added invariant to preserve precondition through loop iterations */
            nums@.len() < 0x8000_0000,
        decreases nums@.len() - i
    {
        if nums[i] == target {
            /* code modified by LLM (iteration 2): simplified assertions using loop invariant */
            assert(i < nums@.len());
            assert(i < 0x8000_0000);
            return i as i32;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 2): added assertion to prove that all elements were checked when returning -1 */
    assert(i == nums@.len());
    assert(forall |j: int| 0 <= j < nums@.len() as int ==> #[trigger]nums@[j] != target);
    return -1;
}
}