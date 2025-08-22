#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
    // pre-conditions-start
    requires
        nums@.len() < 0x8000_0000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret < nums@.len(),
        ret >=0 ==> nums@[ret as int] == target,
        ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i]!= target,
        ret < 0 ==> forall |i: int| 0 <= i < nums@.len() ==> #[trigger]nums@[i] != target,
    // post-conditions-end
{
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall |j: int| 0 <= j < i as int ==> #[trigger]nums@[j] != target,
        /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
        decreases nums.len() - i
    {
        if nums[i] == target {
            /* code modified by LLM (iteration 2): added assertion to help prove postconditions */
            assert(i < nums.len());
            /* code modified by LLM (iteration 2): fixed syntax for sequence length access using parentheses */
            assert(i as int < (nums@).len());
            assert(nums@[i as int] == target);
            return i as i32;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 2): added assertion to help prove postcondition for -1 case */
    assert(forall |j: int| 0 <= j < nums@.len() ==> #[trigger]nums@[j] != target);
    return -1;
}
}

fn main() {}